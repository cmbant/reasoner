module

public import FormalResearch.Asymptotics.SymbolClass
public import FormalResearch.CohnElkies.CardinalAsymptotics
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Positive-Axis Bessel Representation and `CR.16` Bounds (Lemma W.1)

Source: `CFT/sign_uncertainty/paper/ce_cr_airy_wkb_derivatives.tex`, §1 (`cecw:W1`, eqs. `(W.1a)`,
`(CR.16)`).

## Main definitions
* `besselJ ν ζ`: shifted modified Bessel integral `∫_{0}^∞ exp(-ζ (cosh s - 1)) cosh(ν s) ds`.
* `besselP ν ζ`: normalized Bessel integral `ζ^{1/2} besselJ ν ζ`.
* `besselR ζ`: Bessel ratio `besselJ (2/3) ζ / besselJ (1/3) ζ`.
* `eulerDerivOp`, `eulerDeriv`: Euler operator `(x ∂_x)` and its `k`-fold iterate `(x ∂_x)^k`.
* `cohnVSmooth a z`: smooth extension of `cohnV a z = (m(z) - a(z - a)) / (z - a)²` across `z = a`
  with removable value `1 / 2`.
* `cohnCR16F a t`: smooth extension of `t ↦ t * cohnVSmooth a (a₁ + t)` across `t = 0` with
  removable value `(a₁ - a)⁻²`.

## Main results
* Unconditional Bessel model (`0 ≤ ν < 1`, zero DLMF axioms):
  `iteratedDeriv_besselJ`, `abs_iteratedDeriv_besselJ_le` (`(W.1a)`), `besselP_isSymbol`,
  `tendsto_besselP`, `besselR_isSymbolOn`, `isSymbolOn_eulerDeriv`,
  `besselModel_eulerDeriv_bound`.
* Lemma `W.1(b)–(c)` (`(CR.16)`) for `cohnM = airyAi' / airyAi`:
  `cohnM_eulerDeriv_bound`, `cohnVSmooth_contDiffOn`, `cardinal_CR16_smooth`, `cardinal_CR16`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ContDiff Interval Real Topology
open FormalResearch.Asymptotics FormalResearch.Special

namespace FormalResearch.CohnElkies

/-! ### Definitions -/

/-- Shifted modified Bessel integral `J_ν(ζ) = ∫_{0}^∞ exp(-ζ (cosh s - 1)) cosh(ν s) ds`. -/
noncomputable def besselJ (ν ζ : ℝ) : ℝ :=
  ∫ s in Set.Ioi (0 : ℝ), Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)

/-- Normalized Bessel integral `P_ν(ζ) = ζ^{1/2} J_ν(ζ)`. -/
noncomputable def besselP (ν ζ : ℝ) : ℝ :=
  ζ ^ (1 / 2 : ℝ) * besselJ ν ζ

/-- Bessel ratio `R(ζ) = J_{2/3}(ζ) / J_{1/3}(ζ)`. -/
noncomputable def besselR (ζ : ℝ) : ℝ :=
  besselJ (2 / 3) ζ / besselJ (1 / 3) ζ

/-- Euler differential operator `(x ∂_x) f(x) = x f'(x)`. -/
noncomputable def eulerDerivOp (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * _root_.deriv f x

/-- Iterated Euler differential operator `(x ∂_x)^k f`. -/
noncomputable def eulerDeriv (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  eulerDerivOp^[k] f

/-- Smooth extension of `v(z) = (m(z) - a (z - a)) / (z - a)²` with `v(a) = 1 / 2`. -/
noncomputable def cohnVSmooth (a z : ℝ) : ℝ :=
  if z = a then 1 / 2 else cohnV a z

/-- Smooth extension of `t ↦ t v(a₁ + t)` across `t = 0` with `F(0) = (a₁ - a)⁻²`. -/
noncomputable def cohnCR16F (a t : ℝ) : ℝ :=
  if t = 0 then (airyZero 1 - a)⁻¹ ^ 2 else t * cohnVSmooth a (airyZero 1 + t)

/-! ### Elementary `cosh` and Gaussian-tail helpers -/

private lemma nonneg_of_hasDerivAt_nonneg_Ici {f f' : ℝ → ℝ} (hf0 : 0 ≤ f 0)
    (hd : ∀ t : ℝ, HasDerivAt f (f' t) t) (hnn : ∀ t ≥ 0, 0 ≤ f' t) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      fun t ht => by rw [(hd t).deriv]; exact hnn t (interior_subset ht)
  exact hf0.trans (hmono (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx)

private lemma nonneg_of_hasDerivAt_nonneg_Icc {f f' : ℝ → ℝ} (hf0 : 0 ≤ f 0)
    (hd : ∀ t : ℝ, HasDerivAt f (f' t) t) (hnn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f' t)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      fun t ht => by rw [(hd t).deriv]; exact hnn t (interior_subset ht)
  exact hf0.trans (hmono ⟨le_rfl, zero_le_one⟩ hx hx.1)

private lemma cosh_sub_one_ge_half_sq (s : ℝ) : s ^ 2 / 2 ≤ Real.cosh s - 1 := by
  suffices h : ∀ x ≥ 0, x ^ 2 / 2 ≤ Real.cosh x - 1 by
    rcases le_or_gt 0 s with hs | hs
    · exact h s hs
    · simpa [Real.cosh_neg] using h (-s) (by linarith)
  intro x hx
  have h1 : ∀ t ≥ 0, 0 ≤ Real.sinh t - t := fun t ht =>
    nonneg_of_hasDerivAt_nonneg_Ici (by simp)
      (fun u => (Real.hasDerivAt_sinh u).fun_sub (hasDerivAt_id u))
      (fun u _ => by linarith [Real.one_le_cosh u]) ht
  linarith [nonneg_of_hasDerivAt_nonneg_Ici (f := fun t => Real.cosh t - 1 - t ^ 2 / 2)
    (by simp) (fun u => (((Real.hasDerivAt_cosh u).sub_const 1).fun_sub
      ((hasDerivAt_pow 2 u).div_const 2)).congr_deriv (by ring)) h1 hx]

private lemma cosh_sub_one_le_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.cosh s - 1 ≤ s ^ 2 := by
  have hcosh2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.cosh t ≤ 2 := fun t ht => by
    have hexp : Real.exp (t ^ 2 / 2) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2])
    have h2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      rw [← Real.exp_one_rpow (1 / 2 : ℝ)]
      have hsq : (Real.exp 1 ^ (1 / 2 : ℝ)) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.exp_pos 1).le]; norm_num
        linarith [Real.exp_one_lt_d9]
      nlinarith [Real.rpow_nonneg (Real.exp_pos 1).le (1 / 2 : ℝ)]
    exact (Real.cosh_le_exp_half_sq t).trans (hexp.trans h2)
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 2 * t - Real.sinh t := fun t ht =>
    nonneg_of_hasDerivAt_nonneg_Icc (by simp)
      (fun u => ((hasDerivAt_id u).const_mul 2).fun_sub (Real.hasDerivAt_sinh u))
      (fun u hu => by linarith [hcosh2 u hu]) ht
  linarith [nonneg_of_hasDerivAt_nonneg_Icc (f := fun t => t ^ 2 - (Real.cosh t - 1))
    (by simp) (fun u => ((hasDerivAt_pow 2 u).fun_sub
      ((Real.hasDerivAt_cosh u).sub_const 1)).congr_deriv (by ring)) h1 ⟨hs0, hs1⟩]

private lemma cosh_sub_one_le_cube_add_half_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.cosh s - 1 - s ^ 2 / 2 ≤ s ^ 3 := by
  have hsinh6 : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sinh t ≤ 6 := fun t ht => by
    have hs : Real.sinh t ≤ Real.cosh t := by rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-t)]
    have h1 := (Real.cosh_le_exp_half_sq t).trans (Real.exp_le_exp.mpr (by nlinarith [ht.1, ht.2] : t ^ 2 / 2 ≤ 1))
    linarith [Real.exp_one_lt_d9]
  have h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 6 * t - (Real.cosh t - 1) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg_Icc (by simp)
      (fun u => ((hasDerivAt_id u).const_mul 6).fun_sub ((Real.hasDerivAt_cosh u).sub_const 1))
      (fun u hu => by linarith [hsinh6 u hu]) ht
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 3 * t ^ 2 - (Real.sinh t - t) := fun t ht =>
    nonneg_of_hasDerivAt_nonneg_Icc (by simp)
      (fun u => (((hasDerivAt_pow 2 u).const_mul 3).fun_sub
        ((Real.hasDerivAt_sinh u).fun_sub (hasDerivAt_id u))).congr_deriv (by ring)) h2 ht
  linarith [nonneg_of_hasDerivAt_nonneg_Icc (f := fun t => t ^ 3 - (Real.cosh t - 1 - t ^ 2 / 2))
    (by simp) (fun u => ((hasDerivAt_pow 3 u).fun_sub (((Real.hasDerivAt_cosh u).sub_const 1).fun_sub
      ((hasDerivAt_pow 2 u).div_const 2))).congr_deriv (by ring)) h1 ⟨hs0, hs1⟩]

private lemma cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]; linarith [Real.exp_le_exp.mpr (le_abs_self x), Real.exp_le_exp.mpr (neg_le_abs x)]

private lemma integrableOn_exp_neg_mul_sq_add_linear {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s ^ 2 + b * s)) (Set.Ioi 0) := by
  have hsq : ∀ s : ℝ, -a * s ^ 2 + b * s ≤ b ^ 2 / (2 * a) + -(a / 2) * s ^ 2 := fun s => by
    have h0 : 0 ≤ (a / 2) * (s - b / a) ^ 2 := mul_nonneg (half_pos ha).le (sq_nonneg _)
    have h1 : (a / 2) * (s - b / a) ^ 2 = (a / 2) * s ^ 2 - b * s + b ^ 2 / (2 * a) := by
      field_simp; ring
    linarith
  have hdom : IntegrableOn (fun s : ℝ => Real.exp (b ^ 2 / (2 * a)) * Real.exp (-(a / 2) * s ^ 2))
      (Set.Ioi 0) := ((integrable_exp_neg_mul_sq (half_pos ha)).const_mul _).integrableOn
  refine hdom.mono' ((by fun_prop : Continuous fun s : ℝ => Real.exp (-a * s ^ 2 + b * s)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s _ => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (hsq s)

/-! ### Unconditional Lemma W.1 for `besselJ`, `besselP`, `besselR` -/

private noncomputable def besselJInt (k : ℕ) (ν ζ s : ℝ) : ℝ :=
  (Real.cosh s - 1) ^ k * Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)

private noncomputable def besselJDeriv (k : ℕ) (ν ζ : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * ∫ s in Set.Ioi (0 : ℝ), besselJInt k ν ζ s

private lemma besselJInt_nonneg (k : ℕ) (ν ζ s : ℝ) : 0 ≤ besselJInt k ν ζ s :=
  mul_nonneg (mul_nonneg (pow_nonneg (sub_nonneg.mpr (Real.one_le_cosh s)) k)
    (Real.exp_pos _).le) (le_trans zero_le_one (Real.one_le_cosh _))

private lemma integrableOn_besselJInt (k : ℕ) (ν : ℝ) {ζ : ℝ} (hζ : 0 < ζ) :
    IntegrableOn (besselJInt k ν ζ) (Set.Ioi 0) := by
  refine (integrableOn_exp_neg_mul_sq_add_linear (a := ζ / 2) (b := (k : ℝ) + |ν|)
    (half_pos hζ)).mono'
    ((by unfold besselJInt; fun_prop : Continuous (besselJInt k ν ζ)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
  rw [Set.mem_Ioi] at hs
  have hc1 : 0 ≤ Real.cosh s - 1 := sub_nonneg.mpr (Real.one_le_cosh s)
  have hc_exp : Real.cosh s - 1 ≤ Real.exp s := by
    have := cosh_le_exp_abs s; rw [abs_of_pos hs] at this; linarith
  have hpow : (Real.cosh s - 1) ^ k ≤ Real.exp ((k : ℝ) * s) :=
    (pow_le_pow_left₀ hc1 hc_exp k).trans_eq (by rw [← Real.exp_nat_mul])
  have hexp : Real.exp (-ζ * (Real.cosh s - 1)) ≤ Real.exp (-(ζ / 2) * s ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [cosh_sub_one_ge_half_sq s])
  have hnu : Real.cosh (ν * s) ≤ Real.exp (|ν| * s) :=
    (cosh_le_exp_abs _).trans_eq (by rw [abs_mul, abs_of_pos hs])
  rw [Real.norm_eq_abs, abs_of_nonneg (besselJInt_nonneg k ν ζ s)]
  unfold besselJInt
  calc (Real.cosh s - 1) ^ k * Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)
      ≤ Real.exp ((k : ℝ) * s) * Real.exp (-(ζ / 2) * s ^ 2) * Real.exp (|ν| * s) := by gcongr
    _ = Real.exp (-(ζ / 2) * s ^ 2 + ((k : ℝ) + |ν|) * s) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

private lemma hasDerivAt_besselJDeriv (k : ℕ) (ν : ℝ) {ζ₀ : ℝ} (hζ₀ : 0 < ζ₀) :
    HasDerivAt (besselJDeriv k ν) (besselJDeriv (k + 1) ν ζ₀) ζ₀ := by
  have hs : Metric.ball ζ₀ (ζ₀ / 2) ∈ 𝓝 ζ₀ := Metric.ball_mem_nhds ζ₀ (half_pos hζ₀)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (F := fun ζ s => besselJInt k ν ζ s) (F' := fun ζ s => -besselJInt (k + 1) ν ζ s) hs
    (Eventually.of_forall fun ζ =>
      (by unfold besselJInt; fun_prop : Continuous (besselJInt k ν ζ)).aestronglyMeasurable)
    (integrableOn_besselJInt k ν hζ₀)
    (by unfold besselJInt; fun_prop :
      Continuous (fun s => -besselJInt (k + 1) ν ζ₀ s)).aestronglyMeasurable
    (bound := besselJInt (k + 1) ν (ζ₀ / 2))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s _ ζ hζ => by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hζ
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (besselJInt_nonneg _ _ _ _)]
      have hexp : Real.exp (-ζ * (Real.cosh s - 1)) ≤ Real.exp (-(ζ₀ / 2) * (Real.cosh s - 1)) :=
        Real.exp_le_exp.mpr (by nlinarith [sub_nonneg.mpr (Real.one_le_cosh s)])
      unfold besselJInt
      exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (pow_nonneg (sub_nonneg.mpr (Real.one_le_cosh s)) _))
        le_rfl (le_trans zero_le_one (Real.one_le_cosh _))
        (mul_nonneg (pow_nonneg (sub_nonneg.mpr (Real.one_le_cosh s)) _) (Real.exp_pos _).le)))
    (integrableOn_besselJInt (k + 1) ν (half_pos hζ₀))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s _ ζ _ => by
      have hd_exp : HasDerivAt (fun u : ℝ => Real.exp (-u * (Real.cosh s - 1)))
          (-(Real.cosh s - 1) * Real.exp (-ζ * (Real.cosh s - 1))) ζ :=
        (((hasDerivAt_neg ζ).mul_const (Real.cosh s - 1)).exp).congr_deriv (by ring)
      exact ((hd_exp.const_mul ((Real.cosh s - 1) ^ k)).mul_const (Real.cosh (ν * s))).congr_deriv
        (by unfold besselJInt; rw [pow_succ]; ring)))
  refine (key.2.const_mul ((-1 : ℝ) ^ k)).congr_deriv ?_
  rw [integral_neg]; unfold besselJDeriv; rw [pow_succ]; ring

private lemma contDiffOn_besselJDeriv :
    ∀ n k : ℕ, ∀ ν : ℝ, ContDiffOn ℝ n (besselJDeriv k ν) (Set.Ioi 0) := by
  intro n
  induction n with
  | zero =>
    intro k ν; change ContDiffOn ℝ 0 (besselJDeriv k ν) (Set.Ioi 0); rw [contDiffOn_zero]
    exact fun ζ hζ => (hasDerivAt_besselJDeriv k ν hζ).continuousAt.continuousWithinAt
  | succ n ih =>
    intro k ν; rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun ζ hζ => (hasDerivAt_besselJDeriv k ν hζ).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp),
      (ih (k + 1) ν).congr fun ζ hζ => (hasDerivAt_besselJDeriv k ν hζ).deriv⟩

/-- Smoothness of `besselJ ν` on `(0, ∞)`. -/
theorem contDiffOn_besselJ (ν : ℝ) : ContDiffOn ℝ ∞ (besselJ ν) (Set.Ioi 0) := by
  have h0 : besselJDeriv 0 ν = besselJ ν := by ext ζ; simp [besselJDeriv, besselJ, besselJInt]
  rw [← h0, contDiffOn_infty]; exact fun n => contDiffOn_besselJDeriv n 0 ν

/-- **Differentiation under the integral sign for `besselJ`** (Lemma `W.1`). -/
theorem iteratedDeriv_besselJ (ν : ℝ) {ζ : ℝ} (hζ : 0 < ζ) (k : ℕ) :
    iteratedDeriv k (besselJ ν) ζ =
      (-1 : ℝ) ^ k * ∫ s in Set.Ioi (0 : ℝ),
        (Real.cosh s - 1) ^ k * Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s) := by
  have hgen : ∀ k m : ℕ, ∀ {ζ : ℝ}, 0 < ζ →
      iteratedDeriv k (besselJDeriv m ν) ζ = besselJDeriv (k + m) ν ζ := by
    intro k
    induction k with
    | zero => intro m ζ _; simp
    | succ k ih =>
      intro m ζ hζ
      have hev : iteratedDeriv k (besselJDeriv m ν) =ᶠ[𝓝 ζ] besselJDeriv (k + m) ν :=
        Filter.eventually_of_mem (Ioi_mem_nhds hζ) fun u hu => ih m hu
      rw [iteratedDeriv_succ, hev.deriv_eq, (hasDerivAt_besselJDeriv (k + m) ν hζ).deriv, Nat.succ_add]
  have h0 : besselJDeriv 0 ν = besselJ ν := by ext u; simp [besselJDeriv, besselJ, besselJInt]
  rw [← h0, hgen k 0 hζ, add_zero]; rfl

/-- **Eq. `(W.1a)`**: for `0 ≤ ν < 1` and `k : ℕ`, `|J_ν^{(k)}(ζ)| ≤ C_k ζ^{-k - 1/2}` on `[1, ∞)`. -/
theorem abs_iteratedDeriv_besselJ_le {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ ≥ 1,
      |iteratedDeriv k (besselJ ν) ζ| ≤ C * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
  have hint_u : IntegrableOn (fun u : ℝ => u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)) (Set.Ioi 0) := by
    refine (integrableOn_exp_neg_mul_sq_add_linear (a := 1 / 2) (b := (2 * k : ℕ))
      (by norm_num)).mono' (by fun_prop : Continuous fun u : ℝ =>
        u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 ≤ u := (Set.mem_Ioi.mp hu).le
    have hpow : u ^ (2 * k) ≤ Real.exp (((2 * k : ℕ) : ℝ) * u) :=
      (pow_le_pow_left₀ hu0 (by linarith [Real.add_one_le_exp u]) _).trans_eq
        (Real.exp_nat_mul u (2 * k)).symm
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
    calc u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)
        ≤ Real.exp (((2 * k : ℕ) : ℝ) * u) * Real.exp (-(1 / 2) * u ^ 2) := by gcongr
      _ = Real.exp (-(1 / 2) * u ^ 2 + ((2 * k : ℕ) : ℝ) * u) := by rw [← Real.exp_add]; congr 1; ring
  set I₁ : ℝ := ∫ u in Set.Ioi (0 : ℝ), u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)
  set I₂ : ℝ := ∫ s in Set.Ioi (0 : ℝ), besselJInt k ν (1 / 2) s
  have hI₁_nn : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Ioi fun u _ => by rw [pow_mul]; positivity
  have hI₂_nn : 0 ≤ I₂ := setIntegral_nonneg measurableSet_Ioi fun s _ => besselJInt_nonneg k ν (1 / 2) s
  set C₁ : ℝ := Real.cosh 1 * I₁
  set C₂ : ℝ := (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * I₂
  refine ⟨C₁ + C₂, add_nonneg (mul_nonneg (le_trans zero_le_one (Real.one_le_cosh _)) hI₁_nn)
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) hI₂_nn), fun ζ hζ => ?_⟩
  have hζ0 : 0 < ζ := by linarith
  rw [iteratedDeriv_besselJ ν hζ0 k, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  change |∫ s in Set.Ioi (0 : ℝ), besselJInt k ν ζ s| ≤ _
  have hint_full : IntegrableOn (besselJInt k ν ζ) (Set.Ioi 0) := integrableOn_besselJInt k ν hζ0
  have hint_ioc : IntegrableOn (besselJInt k ν ζ) (Set.Ioc 0 1) := hint_full.mono_set Set.Ioc_subset_Ioi_self
  have hint_ioi : IntegrableOn (besselJInt k ν ζ) (Set.Ioi 1) := hint_full.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hsplit : ∫ s in Set.Ioi (0 : ℝ), besselJInt k ν ζ s =
      (∫ s in Set.Ioc (0 : ℝ) 1, besselJInt k ν ζ s) + ∫ s in Set.Ioi (1 : ℝ), besselJInt k ν ζ s := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hint_ioc hint_ioi,
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi fun s _ => besselJInt_nonneg k ν ζ s), hsplit]
  have hbd_ioc : ∫ s in Set.Ioc (0 : ℝ) 1, besselJInt k ν ζ s ≤ C₁ * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
    let g : ℝ → ℝ := fun s => Real.cosh 1 * (s ^ (2 * k) * Real.exp (-(ζ / 2) * s ^ 2))
    have hscale : ∀ s : ℝ, (Real.sqrt ζ * s) ^ (2 * k) * Real.exp (-(1 / 2) * (Real.sqrt ζ * s) ^ 2) =
        ζ ^ k * (s ^ (2 * k) * Real.exp (-(ζ / 2) * s ^ 2)) := fun s => by
      rw [mul_pow, pow_mul, mul_pow, Real.sq_sqrt hζ0.le,
        show -(1 / 2 : ℝ) * (ζ * s ^ 2) = -(ζ / 2) * s ^ 2 by ring, mul_assoc]
    have hg_int_ioi : IntegrableOn g (Set.Ioi 0) := by
      have hchg : IntegrableOn (fun s => (Real.sqrt ζ * s) ^ (2 * k) *
          Real.exp (-(1 / 2) * (Real.sqrt ζ * s) ^ 2)) (Set.Ioi 0) :=
        (integrableOn_Ioi_comp_mul_left_iff
          (fun u => u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)) 0 (Real.sqrt_pos.mpr hζ0)).mpr
          (by simpa [mul_zero] using hint_u)
      have hchg_mul : IntegrableOn (fun s => (Real.cosh 1 / ζ ^ k) *
          ((Real.sqrt ζ * s) ^ (2 * k) * Real.exp (-(1 / 2) * (Real.sqrt ζ * s) ^ 2))) (Set.Ioi 0) :=
        hchg.const_mul _
      refine hchg_mul.congr_fun (fun s _ => ?_) measurableSet_Ioi
      dsimp [g]; rw [hscale s, div_mul_eq_mul_div, mul_left_comm (Real.cosh 1),
        mul_div_cancel_left₀ _ (pow_ne_zero k hζ0.ne')]
    have h1 : ∫ s in Set.Ioc (0 : ℝ) 1, besselJInt k ν ζ s ≤ ∫ s in Set.Ioc (0 : ℝ) 1, g s := by
      refine setIntegral_mono_on hint_ioc (hg_int_ioi.mono_set Set.Ioc_subset_Ioi_self)
        measurableSet_Ioc fun s hs => ?_
      have hs0 : 0 ≤ s := hs.1.le
      have hpow_le : (Real.cosh s - 1) ^ k ≤ s ^ (2 * k) := by
        rw [pow_mul]
        exact pow_le_pow_left₀ (sub_nonneg.mpr (Real.one_le_cosh s)) (cosh_sub_one_le_sq hs0 hs.2) k
      have hexp_le : Real.exp (-ζ * (Real.cosh s - 1)) ≤ Real.exp (-(ζ / 2) * s ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [cosh_sub_one_ge_half_sq s])
      have hnu_le : Real.cosh (ν * s) ≤ Real.cosh 1 := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (mul_nonneg hν0 hs0), abs_of_nonneg zero_le_one]
        nlinarith [hs.1, hs.2]
      unfold besselJInt; dsimp [g]
      calc (Real.cosh s - 1) ^ k * Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)
          ≤ s ^ (2 * k) * Real.exp (-(ζ / 2) * s ^ 2) * Real.cosh 1 :=
            mul_le_mul (mul_le_mul hpow_le hexp_le (Real.exp_pos _).le (pow_nonneg hs0 _)) hnu_le
              (le_trans zero_le_one (Real.one_le_cosh _)) (mul_nonneg (pow_nonneg hs0 _) (Real.exp_pos _).le)
        _ = Real.cosh 1 * (s ^ (2 * k) * Real.exp (-(ζ / 2) * s ^ 2)) := by ring
    have h2 : ∫ s in Set.Ioc (0 : ℝ) 1, g s ≤ ∫ s in Set.Ioi (0 : ℝ), g s :=
      setIntegral_mono_set hg_int_ioi (Eventually.of_forall fun s => by dsimp [g]; rw [pow_mul]; positivity)
        (Eventually.of_forall fun _ h => Set.Ioc_subset_Ioi_self h)
    have h3 : ∫ s in Set.Ioi (0 : ℝ), g s = C₁ * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
      have hchg := integral_comp_mul_left_Ioi
        (fun u : ℝ => u ^ (2 * k) * Real.exp (-(1 / 2) * u ^ 2)) 0 (Real.sqrt_pos.mpr hζ0)
      rw [mul_zero, smul_eq_mul] at hchg
      have heq : ∫ s in Set.Ioi (0 : ℝ), g s = (Real.cosh 1 / ζ ^ k) *
          ∫ s in Set.Ioi (0 : ℝ), (Real.sqrt ζ * s) ^ (2 * k) * Real.exp (-(1 / 2) * (Real.sqrt ζ * s) ^ 2) := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        dsimp [g]; rw [hscale s]; field_simp [pow_ne_zero k hζ0.ne']
      rw [heq, hchg, Real.sqrt_eq_rpow]
      calc (Real.cosh 1 / ζ ^ k) * ((ζ ^ (1 / 2 : ℝ))⁻¹ * I₁)
          = Real.cosh 1 * I₁ * (ζ ^ (-(k : ℝ)) * ζ ^ (-(1 / 2 : ℝ))) := by
              rw [Real.rpow_neg hζ0.le, Real.rpow_neg hζ0.le, Real.rpow_natCast]; ring
        _ = C₁ * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
            rw [← Real.rpow_add hζ0, sub_eq_add_neg]
    exact h1.trans (h2.trans h3.le)
  have hbd_ioi : ∫ s in Set.Ioi (1 : ℝ), besselJInt k ν ζ s ≤ C₂ * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
    have hexp_tail : Real.exp (-ζ / 4) ≤
        (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by
      have hp := Real.pow_div_factorial_le_exp (ζ / 4) (by linarith) (k + 1)
      have h1 : Real.exp (-ζ / 4) ≤
          (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ζ ^ (-((k + 1 : ℕ) : ℝ)) := by
        rw [show -ζ / 4 = -(ζ / 4) by ring, Real.exp_neg, Real.rpow_neg hζ0.le, Real.rpow_natCast]
        calc (Real.exp (ζ / 4))⁻¹ ≤ ((ζ / 4) ^ (k + 1) / ((k + 1).factorial : ℝ))⁻¹ :=
              inv_anti₀ (div_pos (by positivity) (Nat.cast_pos.mpr (Nat.factorial_pos _))) hp
          _ = (4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * (ζ ^ (k + 1))⁻¹ := by
              rw [div_pow, inv_div, div_eq_mul_inv, inv_div, div_eq_mul_inv]; ring
      exact h1.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hζ (by push_cast; linarith)) (by positivity))
    have hint_half : IntegrableOn (besselJInt k ν (1 / 2)) (Set.Ioi 0) :=
      integrableOn_besselJInt k ν (by norm_num)
    have h1 : ∫ s in Set.Ioi (1 : ℝ), besselJInt k ν ζ s ≤
        ∫ s in Set.Ioi (1 : ℝ), Real.exp (-ζ / 4) * besselJInt k ν (1 / 2) s := by
      refine setIntegral_mono_on hint_ioi ((hint_half.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul _)
        measurableSet_Ioi fun s hs => ?_
      rw [Set.mem_Ioi] at hs
      have hc1 : 1 / 2 ≤ Real.cosh s - 1 := by nlinarith [cosh_sub_one_ge_half_sq s]
      have hexp_le : Real.exp (-ζ * (Real.cosh s - 1)) ≤
          Real.exp (-ζ / 4) * Real.exp (-(1 / 2 : ℝ) * (Real.cosh s - 1)) :=
        (Real.exp_le_exp.mpr (by nlinarith)).trans_eq (Real.exp_add _ _)
      unfold besselJInt
      calc (Real.cosh s - 1) ^ k * Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)
          ≤ (Real.cosh s - 1) ^ k * (Real.exp (-ζ / 4) * Real.exp (-(1 / 2 : ℝ) * (Real.cosh s - 1))) *
              Real.cosh (ν * s) := by gcongr
        _ = Real.exp (-ζ / 4) *
              ((Real.cosh s - 1) ^ k * Real.exp (-(1 / 2 : ℝ) * (Real.cosh s - 1)) * Real.cosh (ν * s)) := by ring
    have h2 : ∫ s in Set.Ioi (1 : ℝ), besselJInt k ν (1 / 2) s ≤ I₂ :=
      setIntegral_mono_set hint_half (Eventually.of_forall fun s => besselJInt_nonneg k ν (1 / 2) s)
        (Eventually.of_forall fun _ h => Set.Ioi_subset_Ioi zero_le_one h)
    rw [integral_const_mul] at h1
    calc ∫ s in Set.Ioi (1 : ℝ), besselJInt k ν ζ s
        ≤ Real.exp (-ζ / 4) * I₂ := h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
      _ ≤ ((4 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ)) * I₂ :=
          mul_le_mul_of_nonneg_right hexp_tail hI₂_nn
      _ = C₂ * ζ ^ (-(k : ℝ) - 1 / 2 : ℝ) := by dsimp [C₂]; ring
  linarith

/-- `besselJ ν ∈ 𝒮_{1/2}` on `[1, ∞)` for `0 ≤ ν < 1`. -/
theorem besselJ_isSymbol {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) :
    IsSymbol (1 / 2) (besselJ ν) := by
  refine isSymbolOn_of_contDiffOn_open isOpen_Ioi
    (fun _ h => by rw [Set.mem_Ici] at h; rw [Set.mem_Ioi]; linarith) (contDiffOn_besselJ ν) fun j => ?_
  obtain ⟨C, hC, hbd⟩ := abs_iteratedDeriv_besselJ_le hν0 hν1 j
  exact ⟨C, hC, fun ζ hζ => by rw [show -(1 / 2 : ℝ) - (j : ℝ) = -(j : ℝ) - 1 / 2 by ring]; exact hbd ζ hζ⟩

/-- `besselP ν ∈ 𝒮_0` on `[1, ∞)` for `0 ≤ ν < 1`. -/
theorem besselP_isSymbol {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) :
    IsSymbol 0 (besselP ν) := by
  have h2 := (IsSymbol.rpow (1 / 2)).mul (besselJ_isSymbol hν0 hν1)
  rwa [neg_add_cancel] at h2

/-- Limit `P_ν(ζ) → √(π / 2)` as `ζ → ∞` (`0 ≤ ν < 1`). -/
theorem tendsto_besselP {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) :
    Filter.Tendsto (besselP ν) Filter.atTop (𝓝 √(Real.pi / 2)) := by
  let G : ℝ → ℝ → ℝ := fun ζ σ =>
    Real.exp (-ζ * (Real.cosh (σ / Real.sqrt ζ) - 1)) * Real.cosh (ν * (σ / Real.sqrt ζ))
  have hP_eq : ∀ᶠ ζ in Filter.atTop, besselP ν ζ = ∫ σ in Set.Ioi (0 : ℝ), G ζ σ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with ζ hζ
    have hζ0 : 0 < ζ := by linarith
    have hchg := integral_comp_mul_left_Ioi
      (fun s => Real.exp (-ζ * (Real.cosh s - 1)) * Real.cosh (ν * s)) 0
      (inv_pos.mpr (Real.sqrt_pos.mpr hζ0))
    rw [mul_zero, inv_inv, smul_eq_mul] at hchg
    unfold besselP besselJ; rw [← Real.sqrt_eq_rpow, ← hchg]
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ => ?_
    dsimp [G]; simp only [div_eq_inv_mul]
  have hbound_int : IntegrableOn (fun σ : ℝ => Real.exp (-σ ^ 2 / 2) * Real.cosh σ) (Set.Ioi 0) := by
    refine (integrableOn_exp_neg_mul_sq_add_linear (a := 1 / 2) (b := 1) (by norm_num)).mono'
      (by fun_prop : Continuous fun σ : ℝ =>
        Real.exp (-σ ^ 2 / 2) * Real.cosh σ).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_)
    rw [Set.mem_Ioi] at hσ
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)))]
    have hc := cosh_le_exp_abs σ; rw [abs_of_pos hσ] at hc
    calc Real.exp (-σ ^ 2 / 2) * Real.cosh σ
        ≤ Real.exp (-σ ^ 2 / 2) * Real.exp σ := by gcongr
      _ = Real.exp (-(1 / 2) * σ ^ 2 + 1 * σ) := by rw [← Real.exp_add]; congr 1; ring
  have hgauss : ∫ σ in Set.Ioi (0 : ℝ), Real.exp (-σ ^ 2 / 2) = √(Real.pi / 2) := by
    have h := integral_gaussian_Ioi (1 / 2 : ℝ)
    rw [show (fun σ : ℝ => Real.exp (-(1 / 2 : ℝ) * σ ^ 2)) = (fun σ : ℝ => Real.exp (-σ ^ 2 / 2))
      from funext fun σ => by congr 1; ring] at h
    rw [h, show Real.pi / (1 / 2 : ℝ) = 4 * (Real.pi / 2) by ring,
      Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    ring
  rw [← hgauss]
  refine Filter.Tendsto.congr' (hP_eq.mono fun ζ h => h.symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun σ => Real.exp (-σ ^ 2 / 2) * Real.cosh σ)
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with ζ _; exact (by fun_prop : Continuous (G ζ)).aestronglyMeasurable)
    ?_ hbound_int ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ζ hζ
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_)
    rw [Set.mem_Ioi] at hσ
    have hζ0 : 0 < ζ := by linarith
    have hsq_ge : 1 ≤ Real.sqrt ζ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hζ
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one (Real.one_le_cosh _)))]
    have hexp_le : Real.exp (-ζ * (Real.cosh (σ / Real.sqrt ζ) - 1)) ≤ Real.exp (-σ ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have hcosh := cosh_sub_one_ge_half_sq (σ / Real.sqrt ζ)
      rw [div_pow, Real.sq_sqrt hζ0.le] at hcosh
      have hmul : σ ^ 2 / 2 ≤ ζ * (Real.cosh (σ / √ζ) - 1) := by
        calc σ ^ 2 / 2 = ζ * (σ ^ 2 / ζ / 2) := by field_simp [hζ0.ne']
          _ ≤ ζ * (Real.cosh (σ / √ζ) - 1) := mul_le_mul_of_nonneg_left hcosh hζ0.le
      linarith
    have hcosh_le : Real.cosh (ν * (σ / Real.sqrt ζ)) ≤ Real.cosh σ := by
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_pos hσ]
      nlinarith [div_le_self hσ.le hsq_ge]
    exact mul_le_mul hexp_le hcosh_le (le_trans zero_le_one (Real.one_le_cosh _)) (Real.exp_pos _).le
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun σ hσ => ?_)
    rw [Set.mem_Ioi] at hσ
    have hsqrt_tendsto : Filter.Tendsto (fun ζ : ℝ => σ / Real.sqrt ζ) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_id)
    have hcosh_nu : Filter.Tendsto (fun ζ : ℝ => Real.cosh (ν * (σ / Real.sqrt ζ))) Filter.atTop (𝓝 1) := by
      simpa [Function.comp_def] using Real.continuous_cosh.continuousAt.tendsto.comp (hsqrt_tendsto.const_mul ν)
    have hexp_lim : Filter.Tendsto (fun ζ : ℝ => Real.exp (-ζ * (Real.cosh (σ / Real.sqrt ζ) - 1)))
        Filter.atTop (𝓝 (Real.exp (-σ ^ 2 / 2))) := by
      apply Real.continuous_exp.continuousAt.tendsto.comp
      have hq : Filter.Tendsto (fun u : ℝ => (Real.cosh u - 1) / u ^ 2) (𝓝[>] 0) (𝓝 (1 / 2)) := by
        have hbd : ∀ᶠ u in 𝓝[>] (0 : ℝ),
            1 / 2 ≤ (Real.cosh u - 1) / u ^ 2 ∧ (Real.cosh u - 1) / u ^ 2 ≤ 1 / 2 + u := by
          filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
          have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu.1
          exact ⟨(le_div_iff₀ hu2).mpr (by linarith [cosh_sub_one_ge_half_sq u]),
            (div_le_iff₀ hu2).mpr (by
              linarith [cosh_sub_one_le_cube_add_half_sq hu.1.le hu.2.le,
                show (1 / 2 + u) * u ^ 2 = u ^ 2 / 2 + u ^ 3 by ring])⟩
        have hhi : Filter.Tendsto (fun u : ℝ => 1 / 2 + u) (𝓝[>] 0) (𝓝 (1 / 2)) := by
          simpa using (continuousAt_const.fun_add continuousAt_id :
            Filter.Tendsto (fun u : ℝ => (1 / 2 : ℝ) + u) (𝓝 0) (𝓝 (1 / 2 + 0))).mono_left nhdsWithin_le_nhds
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhi
          (hbd.mono fun _ hu => hu.1) (hbd.mono fun _ hu => hu.2)
      have hu_gt : Filter.Tendsto (fun ζ : ℝ => σ / Real.sqrt ζ) Filter.atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨hsqrt_tendsto, by
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with ζ hζ; exact div_pos hσ (Real.sqrt_pos.mpr hζ)⟩
      have hcomp := (hq.comp hu_gt).const_mul (-σ ^ 2)
      rw [show -σ ^ 2 * (1 / 2 : ℝ) = -σ ^ 2 / 2 by ring] at hcomp
      refine hcomp.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with ζ hζ
      rw [Function.comp_apply, div_pow, Real.sq_sqrt hζ.le]; field_simp
    simpa [G] using hexp_lim.mul hcosh_nu

/-- `besselR = J_{2/3} / J_{1/3} ∈ 𝒮_0` on `[ζ₀, ∞)` for a large enough `ζ₀ ≥ 1`. -/
theorem besselR_isSymbolOn :
    ∃ ζ₀ ≥ 1, (∀ ζ ≥ ζ₀, 0 < besselP (1 / 3) ζ) ∧ IsSymbolOn ζ₀ 0 besselR := by
  set c : ℝ := √(Real.pi / 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (half_pos Real.pi_pos)
  obtain ⟨ζ₁, hζ₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_besselP (ν := 1 / 3) (by norm_num) (by norm_num)).eventually (Ici_mem_nhds (half_lt_self hc)))
  set ζ₀ : ℝ := max 1 ζ₁
  have hζ₀_ge : 1 ≤ ζ₀ := le_max_left 1 ζ₁
  have hζ₀_pos : 0 < ζ₀ := by linarith
  have hP13_sym := (besselP_isSymbol (ν := 1 / 3) (by norm_num) (by norm_num)).to_isSymbolOn hζ₀_ge
  have hP23_sym := (besselP_isSymbol (ν := 2 / 3) (by norm_num) (by norm_num)).to_isSymbolOn hζ₀_ge
  obtain ⟨M, _, hM_bd⟩ := hP13_sym.abs_le
  set F : ℝ → ℝ := fun ζ => besselP (1 / 3) ζ - c
  have hF_sym : IsSymbolOn ζ₀ 0 F := by
    have hsub := hP13_sym.sub hζ₀_pos (IsSymbolOn.const hζ₀_pos le_rfl c)
    rwa [min_self] at hsub
  set b' : ℝ := max 0 (M - c)
  have hF_range : ∀ ζ ≥ ζ₀, F ζ ∈ Set.Icc (-c / 2) b' := fun ζ hζ => by
    have hlow : c / 2 ≤ besselP (1 / 3) ζ := hζ₁ ζ (le_trans (le_max_right 1 ζ₁) hζ)
    have hup : besselP (1 / 3) ζ ≤ M := by
      have := hM_bd ζ hζ; simp only [neg_zero, Real.rpow_zero, mul_one] at this
      exact (le_abs_self _).trans this
    exact ⟨by dsimp [F]; linarith, le_trans (by dsimp [F]; linarith) (le_max_right _ _)⟩
  have hG_cd : ContDiffOn ℝ ∞ (fun w : ℝ => (c + w)⁻¹) (Set.Ioo (-c) (b' + 1)) :=
    ((contDiff_const.add contDiff_id).contDiffOn).inv fun w hw => by dsimp; linarith [hw.1]
  have hcomp := hF_sym.comp_sub_zero hζ₀_pos le_rfl (a := -c) (a' := -c / 2) (b' := b') (b := b' + 1)
    (by linarith) (by linarith) (le_max_left _ _) (by linarith) hF_range hG_cd
  have hinv_sym : IsSymbolOn ζ₀ 0 (fun ζ => (besselP (1 / 3) ζ)⁻¹) :=
    (hcomp.add_same (IsSymbolOn.const hζ₀_pos le_rfl c⁻¹)).congr fun ζ _ => by dsimp [F]; ring
  have hR_sym : IsSymbolOn ζ₀ 0 besselR := by
    have hmul := hP23_sym.mul hζ₀_pos hinv_sym
    rw [add_zero] at hmul
    refine hmul.congr fun ζ hζ => ?_
    have hpow_ne : ζ ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (lt_of_lt_of_le hζ₀_pos hζ) _).ne'
    unfold besselR besselP; rw [← div_eq_mul_inv, mul_div_mul_left _ _ hpow_ne]
  exact ⟨ζ₀, hζ₀_ge, fun ζ hζ => lt_of_lt_of_le (half_pos hc) (hζ₁ ζ (le_trans (le_max_right 1 ζ₁) hζ)), hR_sym⟩

/-! ### Euler differential operator `(x ∂_x)^k` and symbol classes -/

private lemma eulerDeriv_succ (k : ℕ) (f : ℝ → ℝ) :
    eulerDeriv (k + 1) f = eulerDerivOp (eulerDeriv k f) :=
  Function.iterate_succ_apply' eulerDerivOp k f

private lemma eulerDeriv_succ' (k : ℕ) (f : ℝ → ℝ) :
    eulerDeriv (k + 1) f = eulerDeriv k (eulerDerivOp f) :=
  Function.iterate_succ_apply eulerDerivOp k f

private lemma eulerDerivOp_contDiffOn {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (eulerDerivOp f) U :=
  contDiffOn_id.mul (hfU.deriv_of_isOpen hU (by simp))

private lemma eulerDeriv_contDiffOn {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ ∞ f U) (k : ℕ) : ContDiffOn ℝ ∞ (eulerDeriv k f) U := by
  induction k with
  | zero => exact hfU
  | succ k ih => rw [eulerDeriv_succ]; exact eulerDerivOp_contDiffOn hU ih

/-- `eulerDerivOp` preserves `IsSymbolOn x₀ β` when `f` is `C^∞` on an open superset `U ⊇ [x₀, ∞)`. -/
theorem isSymbolOn_eulerDeriv {x₀ β : ℝ} {U : Set ℝ} {f : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hU : IsOpen U) (hsub : Set.Ici x₀ ⊆ U) (hfU : ContDiffOn ℝ ∞ f U)
    (hf : IsSymbolOn x₀ β f) : IsSymbolOn x₀ β (eulerDerivOp f) := by
  have hx : IsSymbolOn x₀ (-1) (fun x : ℝ => x) := by simpa using IsSymbolOn.rpow hx₀ (1 : ℝ)
  have hmul := hx.mul hx₀ (hf.deriv hU hsub hfU)
  rwa [show (-1 : ℝ) + (β + 1) = β by ring] at hmul

/-- Iterated `eulerDeriv k` preserves `IsSymbolOn x₀ β` when `f` is `C^∞` on `U ⊇ [x₀, ∞)`. -/
theorem isSymbolOn_eulerDeriv_iter {x₀ β : ℝ} {U : Set ℝ} {f : ℝ → ℝ} (hx₀ : 0 < x₀)
    (hU : IsOpen U) (hsub : Set.Ici x₀ ⊆ U) (hfU : ContDiffOn ℝ ∞ f U)
    (hf : IsSymbolOn x₀ β f) (k : ℕ) : IsSymbolOn x₀ β (eulerDeriv k f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [eulerDeriv_succ]; exact isSymbolOn_eulerDeriv hx₀ hU hsub (eulerDeriv_contDiffOn hU hfU k) ih

private lemma eulerDeriv_congr_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U)
    (hfg : Set.EqOn f g U) (k : ℕ) : Set.EqOn (eulerDeriv k f) (eulerDeriv k g) U := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k f =ᶠ[𝓝 x] eulerDeriv k g := Filter.eventually_of_mem (hU.mem_nhds hx) ih
    rw [hev.deriv_eq]

private lemma eulerDeriv_add_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => f y + g y) x = eulerDeriv k f x + eulerDeriv k g x := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => f y + g y) =ᶠ[𝓝 x] (fun y => eulerDeriv k f y + eulerDeriv k g y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [hev.deriv_eq]
    have df := (((eulerDeriv_contDiffOn hU hfU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    have dg := (((eulerDeriv_contDiffOn hU hgU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    rw [(df.fun_add dg).deriv]; ring

private lemma eulerDeriv_const_mul_open {U : Set ℝ} {f : ℝ → ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ ∞ f U) (c : ℝ) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => c * f y) x = c * eulerDeriv k f x := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => c * f y) =ᶠ[𝓝 x] (fun y => c * eulerDeriv k f y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [hev.deriv_eq]
    have df := (((eulerDeriv_contDiffOn hU hfU k).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
    rw [(df.const_mul c).deriv]; ring

private lemma eulerDeriv_mul_open {U : Set ℝ} {f g : ℝ → ℝ} (hU : IsOpen U)
    (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U) (k : ℕ) :
    ∀ x ∈ U, eulerDeriv k (fun y => f y * g y) x =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i) g x := by
  induction k with
  | zero => intro x _; simp [eulerDeriv]
  | succ k ih =>
    intro x hx; simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => ∑ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * eulerDeriv i f y * eulerDeriv (k - i) g y) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) (fun y hy => ih y hy)
    rw [hev.deriv_eq]
    have hterm_hd : ∀ i ∈ Finset.range (k + 1),
        HasDerivAt (fun y => (k.choose i : ℝ) * eulerDeriv i f y * eulerDeriv (k - i) g y)
          ((k.choose i : ℝ) * _root_.deriv (eulerDeriv i f) x * eulerDeriv (k - i) g x +
            (k.choose i : ℝ) * eulerDeriv i f x * _root_.deriv (eulerDeriv (k - i) g) x) x := by
      intro i _
      have df := (((eulerDeriv_contDiffOn hU hfU i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
      have dg := (((eulerDeriv_contDiffOn hU hgU (k - i)).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
      exact ((df.const_mul (k.choose i : ℝ)).fun_mul dg).congr_deriv (by ring)
    rw [(HasDerivAt.fun_sum hterm_hd).deriv, Finset.mul_sum]
    have hsplit : ∑ i ∈ Finset.range (k + 1),
        x * ((k.choose i : ℝ) * _root_.deriv (eulerDeriv i f) x * eulerDeriv (k - i) g x +
          (k.choose i : ℝ) * eulerDeriv i f x * _root_.deriv (eulerDeriv (k - i) g) x) =
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) +
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i + 1) g x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by simp only [eulerDeriv_succ, eulerDerivOp, Nat.succ_sub_succ]; ring
    rw [hsplit]
    have hs2 : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i + 1) g x =
        eulerDeriv 0 f x * eulerDeriv (k + 1) g x +
          ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x := by
      rw [Finset.sum_range_succ']; simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, add_comm]
      exact congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => by
        have hik : i + 1 ≤ k := Finset.mem_range.mp hi; congr 2; omega)
    have hlast : ∑ i ∈ Finset.range (k + 1),
        (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x =
        ∑ i ∈ Finset.range k, (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x := by
      rw [Finset.sum_range_succ]; simp [Nat.choose_succ_self]
    rw [hs2, ← hlast]; symm; rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    rw [add_comm (eulerDeriv 0 f x * eulerDeriv (k + 1) g x)]
    have hcomb : ∑ i ∈ Finset.range (k + 1),
        ((k + 1).choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x =
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) +
        (∑ i ∈ Finset.range (k + 1), (k.choose (i + 1) : ℝ) * eulerDeriv (i + 1) f x * eulerDeriv (k + 1 - (i + 1)) g x) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.choose_succ_succ', Nat.cast_add]; ring
    rw [hcomb]; ring

private lemma eulerDeriv_mul_bound {U : Set ℝ} (hU : IsOpen U) {f g : ℝ → ℝ}
    (hfU : ContDiffOn ℝ ∞ f U) (hgU : ContDiffOn ℝ ∞ g U) {k : ℕ} {x : ℝ} (hx : x ∈ U)
    {A B : ℕ → ℝ} {w₁ w₂ : ℝ}
    (hf : ∀ i ≤ k, |eulerDeriv i f x| ≤ A i * w₁)
    (hg : ∀ i ≤ k, |eulerDeriv i g x| ≤ B i * w₂) :
    |eulerDeriv k (fun y => f y * g y) x| ≤
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)) * (w₁ * w₂) := by
  rw [eulerDeriv_mul_open hU hfU hgU k x hx]
  calc |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i) g x|
      ≤ ∑ i ∈ Finset.range (k + 1), |(k.choose i : ℝ) * eulerDeriv i f x * eulerDeriv (k - i) g x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℝ) * A i * B (k - i)) * (w₁ * w₂) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have h1 := hf i hik
        have h2 := hg (k - i) (Nat.sub_le k i)
        have h12 := mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        calc (k.choose i : ℝ) * |eulerDeriv i f x| * |eulerDeriv (k - i) g x|
            = (k.choose i : ℝ) * (|eulerDeriv i f x| * |eulerDeriv (k - i) g x|) := by ring
          _ ≤ (k.choose i : ℝ) * ((A i * w₁) * (B (k - i) * w₂)) :=
              mul_le_mul_of_nonneg_left h12 (Nat.cast_nonneg _)
          _ = ((k.choose i : ℝ) * A i * B (k - i)) * (w₁ * w₂) := by ring
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * A i * B (k - i)) * (w₁ * w₂) := by
        rw [← Finset.sum_mul]

private lemma eulerDeriv_neg_sqrt (k : ℕ) {z : ℝ} (hz : 0 < z) :
    eulerDeriv k (fun y => -Real.sqrt y) z = -(1 / 2 : ℝ) ^ k * Real.sqrt z := by
  induction k generalizing z with
  | zero => simp [eulerDeriv]
  | succ k ih =>
    simp only [eulerDeriv_succ, eulerDerivOp]
    have hev : eulerDeriv k (fun y => -Real.sqrt y) =ᶠ[𝓝 z] (fun y => -(1 / 2 : ℝ) ^ k * Real.sqrt y) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hz) fun y hy => ih hy
    rw [hev.deriv_eq, ((Real.hasDerivAt_sqrt hz.ne').const_mul (-(1 / 2 : ℝ) ^ k)).deriv]
    have hsq : z * (1 / (2 * Real.sqrt z)) = (1 / 2 : ℝ) * Real.sqrt z := by
      calc z * (1 / (2 * Real.sqrt z)) = (Real.sqrt z * Real.sqrt z) * (1 / (2 * Real.sqrt z)) := by
            rw [Real.mul_self_sqrt hz.le]
        _ = (1 / 2 : ℝ) * Real.sqrt z := by field_simp [(Real.sqrt_pos.mpr hz).ne']
    rw [show z * (-(1 / 2 : ℝ) ^ k * (1 / (2 * Real.sqrt z))) =
      -(1 / 2 : ℝ) ^ k * (z * (1 / (2 * Real.sqrt z))) by ring, hsq, pow_succ]; ring

private lemma eulerDeriv_comp_rpow {ζ₀ c p : ℝ} (_hζ₀ : 0 < ζ₀) (_hc : 0 < c) (_hp : 0 < p) :
    ∀ k : ℕ, ∀ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Set.Ioi ζ₀) →
      ∀ {z : ℝ}, ζ₀ < c * z ^ p → 0 < z →
        eulerDeriv k (fun y => g (c * y ^ p)) z = p ^ k * eulerDeriv k g (c * z ^ p) := by
  intro k
  induction k with
  | zero => intro g _ z _ _; simp [eulerDeriv]
  | succ k ih =>
    intro g hg z hcz hz
    let U₀ : Set ℝ := {y : ℝ | 0 < y ∧ ζ₀ < c * y ^ p}
    have hU₀_open : IsOpen U₀ := isOpen_iff_mem_nhds.mpr fun y hy =>
      Filter.inter_mem (Ioi_mem_nhds hy.1)
        ((continuousAt_const.mul (Real.continuousAt_rpow_const y p (Or.inl hy.1.ne'))).preimage_mem_nhds
          (Ioi_mem_nhds hy.2))
    have heq_op : Set.EqOn (eulerDerivOp (fun y => g (c * y ^ p)))
        (fun y => p * eulerDerivOp g (c * y ^ p)) U₀ := fun y hy => by
      have hcy : HasDerivAt (fun x : ℝ => c * x ^ p) (c * (p * y ^ (p - 1))) y :=
        (Real.hasDerivAt_rpow_const (Or.inl hy.1.ne')).const_mul c
      have hg_at : HasDerivAt g (_root_.deriv g (c * y ^ p)) (c * y ^ p) :=
        ((hg.contDiffAt (Ioi_mem_nhds hy.2)).differentiableAt (by simp)).hasDerivAt
      have hcomp : HasDerivAt (fun x => g (c * x ^ p))
          (_root_.deriv g (c * y ^ p) * (c * (p * y ^ (p - 1)))) y := hg_at.comp y hcy
      unfold eulerDerivOp; rw [hcomp.deriv]
      have hpow : y * y ^ (p - 1) = y ^ p := by rw [Real.rpow_sub_one hy.1.ne']; field_simp [hy.1.ne']
      calc y * (_root_.deriv g (c * y ^ p) * (c * (p * y ^ (p - 1))))
          = p * (c * (y * y ^ (p - 1)) * _root_.deriv g (c * y ^ p)) := by ring
        _ = p * (c * y ^ p * _root_.deriv g (c * y ^ p)) := by rw [hpow]
    have hcomp_cd : ContDiffOn ℝ ∞ (fun y => eulerDerivOp g (c * y ^ p)) U₀ :=
      (eulerDerivOp_contDiffOn isOpen_Ioi hg).comp (fun y hy => ((contDiffAt_const).mul
        (Real.contDiffAt_rpow_const_of_ne hy.1.ne')).contDiffWithinAt) (fun _ hy => hy.2)
    have hzU₀ : z ∈ U₀ := ⟨hz, hcz⟩
    simp only [eulerDeriv_succ']
    rw [eulerDeriv_congr_open hU₀_open heq_op k hzU₀,
      eulerDeriv_const_mul_open hU₀_open hcomp_cd p k z hzU₀,
      ih (eulerDerivOp g) (eulerDerivOp_contDiffOn isOpen_Ioi hg) hcz hz, pow_succ']; ring

/-- **Bessel model Euler-derivative bound** (Lemma `W.1`):
`|(z ∂_z)^k (-√z R((2/3) z^{3/2}))| ≤ C_k √z` for `z ≥ z₀`. -/
theorem besselModel_eulerDeriv_bound :
    ∃ z₀ ≥ 1, ∀ k : ℕ, ∃ C ≥ 0, ∀ z ≥ z₀,
      |eulerDeriv k (fun y => -Real.sqrt y * besselR ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ))) z| ≤
        C * Real.sqrt z := by
  obtain ⟨ζ₀, hζ₀_ge, hPpos, hR_sym⟩ := besselR_isSymbolOn
  have hζ₀_pos : 0 < ζ₀ := by linarith
  have hJ13_pos : ∀ ζ ≥ ζ₀, 0 < besselJ (1 / 3) ζ := fun ζ hζ =>
    pos_of_mul_pos_right (hPpos ζ hζ) (Real.rpow_pos_of_pos (lt_of_lt_of_le hζ₀_pos hζ) _).le
  have hR_cd : ContDiffOn ℝ ∞ besselR (Set.Ioi ζ₀) :=
    ((contDiffOn_besselJ (2 / 3)).mono (Set.Ioi_subset_Ioi hζ₀_pos.le)).div
      ((contDiffOn_besselJ (1 / 3)).mono (Set.Ioi_subset_Ioi hζ₀_pos.le))
      fun ζ hζ => (hJ13_pos ζ hζ.le).ne'
  set ζ₁ : ℝ := ζ₀ + 1
  have hR_ed : ∀ j : ℕ, ∃ D ≥ 0, ∀ ζ ≥ ζ₁, |eulerDeriv j besselR ζ| ≤ D := fun j => by
    have hs := isSymbolOn_eulerDeriv_iter (x₀ := ζ₁) (by linarith) isOpen_Ioi
      (fun ζ hζ => by rw [Set.mem_Ici] at hζ; rw [Set.mem_Ioi]; exact lt_of_lt_of_le (lt_add_one ζ₀) hζ)
      hR_cd (hR_sym.mono_domain (by linarith)) j
    obtain ⟨D, hD, hbd⟩ := hs.abs_le
    exact ⟨D, hD, fun ζ hζ => by simpa using hbd ζ hζ⟩
  set z₀ : ℝ := max 1 ((3 / 2 * ζ₁) ^ (2 / 3 : ℝ) + 1)
  refine ⟨z₀, le_max_left _ _, fun k => ?_⟩
  choose D hD_nn hD using hR_ed
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (1 / 2 : ℝ) ^ i * ((3 / 2 : ℝ) ^ (k - i) * D (k - i)),
    Finset.sum_nonneg fun i _ => by positivity [hD_nn (k - i)], fun z hz => ?_⟩
  have hz_pos : 0 < z := by linarith [le_max_left (1 : ℝ) ((3 / 2 * ζ₁) ^ (2 / 3 : ℝ) + 1)]
  let U_z : Set ℝ := {y : ℝ | 0 < y ∧ ζ₀ < (2 / 3 : ℝ) * y ^ (3 / 2 : ℝ)}
  have hU_z_open : IsOpen U_z := isOpen_iff_mem_nhds.mpr fun y hy =>
    Filter.inter_mem (Ioi_mem_nhds hy.1)
      ((continuousAt_const.mul (Real.continuousAt_rpow_const y (3 / 2 : ℝ) (Or.inl hy.1.ne'))).preimage_mem_nhds
        (Ioi_mem_nhds hy.2))
  have hz_rpow : ζ₁ ≤ (2 / 3 : ℝ) * z ^ (3 / 2 : ℝ) := by
    have hz_ge : (3 / 2 * ζ₁) ^ (2 / 3 : ℝ) ≤ z := by
      linarith [le_max_right (1 : ℝ) ((3 / 2 * ζ₁) ^ (2 / 3 : ℝ) + 1)]
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hz_ge (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [← Real.rpow_mul (by positivity)] at hpow; norm_num at hpow; linarith
  have hsqrt_cd : ContDiffOn ℝ ∞ (fun y : ℝ => -Real.sqrt y) U_z :=
    ContDiffOn.neg fun y hy => (Real.contDiffAt_sqrt hy.1.ne').contDiffWithinAt
  have hcomp_cd : ContDiffOn ℝ ∞ (fun y : ℝ => besselR ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ))) U_z :=
    hR_cd.comp (fun y hy => ((contDiffAt_const).mul
      (Real.contDiffAt_rpow_const_of_ne hy.1.ne')).contDiffWithinAt) (fun _ hy => hy.2)
  have hbd := eulerDeriv_mul_bound hU_z_open hsqrt_cd hcomp_cd (k := k) (x := z) ⟨hz_pos, by linarith⟩
    (A := fun i => (1 / 2 : ℝ) ^ i) (B := fun j => (3 / 2 : ℝ) ^ j * D j)
    (w₁ := Real.sqrt z) (w₂ := 1)
    (fun i _ => by rw [eulerDeriv_neg_sqrt i hz_pos, abs_mul, abs_neg, abs_pow,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (Real.sqrt_nonneg z)])
    (fun j _ => by
      rw [eulerDeriv_comp_rpow hζ₀_pos (by norm_num) (by norm_num) j besselR hR_cd (by linarith) hz_pos,
        abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), mul_one]
      exact mul_le_mul_of_nonneg_left (hD j _ hz_rpow) (by positivity))
  simpa only [mul_one] using hbd

/-! ### Hadamard quotient helper for removable singularities -/

private noncomputable def hadamardInt (c : ℝ) (w f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, w t * f (c + t * (x - c))

private lemma hadamardInt_hasDerivAt {lo c : ℝ} (hc : lo < c) {w f : ℝ → ℝ}
    (hw : ContinuousOn w (Set.Icc 0 1)) (hf : ContDiffOn ℝ ∞ f (Set.Ioi lo))
    {x₀ : ℝ} (hx₀ : lo < x₀) :
    HasDerivAt (hadamardInt c w f) (hadamardInt c (fun t => t * w t) (_root_.deriv f) x₀) x₀ := by
  set δ : ℝ := (x₀ - lo) / 2
  have hδ : 0 < δ := half_pos (sub_pos.mpr hx₀)
  set a' : ℝ := min c (x₀ - δ); set b' : ℝ := max c (x₀ + δ)
  have hsub : Set.Icc a' b' ⊆ Set.Ioi lo := fun _ hy => lt_of_lt_of_le (lt_min hc (by dsimp [δ]; linarith)) hy.1
  have hmem : ∀ x ∈ Metric.ball x₀ δ, ∀ t ∈ Set.Icc (0 : ℝ) 1, c + t * (x - c) ∈ Set.Icc a' b' := fun x hx t ht => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    rw [show c + t * (x - c) = (1 - t) * c + t * x by ring]
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    exact ⟨by nlinarith [ht.1, ht1, min_le_left c (x₀ - δ), min_le_right c (x₀ - δ)],
      by nlinarith [ht.1, ht1, le_max_left c (x₀ + δ), le_max_right c (x₀ + δ)]⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hsub)
  obtain ⟨W, hW⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  set B : ℝ := max W 0 * max M 0
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable
      (fun t => w t * f (c + t * (x - c))) (volume.restrict (Ι 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    rw [Set.uIoc_of_le zero_le_one]
    exact ((hw.mul (hf.continuousOn.comp (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun t ht => hsub (hmem x hx t ht))).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (fun t => w t * f (c + t * (x₀ - c))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact hw.mul (hf.continuousOn.comp (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun t ht => hsub (hmem x₀ (Metric.mem_ball_self hδ) t ht))
  have hF'_meas : AEStronglyMeasurable
      (fun t => (t * w t) * _root_.deriv f (c + t * (x₀ - c))) (volume.restrict (Ι 0 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    exact (((continuousOn_id.mul hw).mul ((hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).comp
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun t ht => hsub (hmem x₀ (Metric.mem_ball_self hδ) t ht))).mono
        Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t => w t * f (c + t * (x - c))) (F' := fun x t => (t * w t) * _root_.deriv f (c + t * (x - c)))
    (bound := fun _ => B) (Metric.ball_mem_nhds x₀ hδ) hF_meas hF_int hF'_meas
    (Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le zero_le_one] at ht; have htIcc := Set.Ioc_subset_Icc_self ht
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg htIcc.1]
      have hwbd : |w t| ≤ max W 0 := (hW t htIcc).trans (le_max_left _ _)
      have hfbd : |_root_.deriv f (c + t * (x - c))| ≤ max M 0 :=
        (hM (c + t * (x - c)) (hmem x hx t htIcc)).trans (le_max_left _ _)
      calc t * |w t| * |_root_.deriv f (c + t * (x - c))| ≤ 1 * max W 0 * max M 0 := by gcongr; exact htIcc.2
        _ = B := by dsimp [B]; ring)
    intervalIntegrable_const
    (Eventually.of_forall fun t ht x hx => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      have hdf : HasDerivAt f (_root_.deriv f (c + t * (x - c))) (c + t * (x - c)) :=
        ((hf.contDiffAt (Ioi_mem_nhds (hsub (hmem x hx t (Set.Ioc_subset_Icc_self ht))))).differentiableAt
          (by simp)).hasDerivAt
      have harg : HasDerivAt (fun y : ℝ => c + t * (y - c)) t x := by
        simpa using (hasDerivAt_const x c).fun_add (((hasDerivAt_id x).sub_const c).const_mul t)
      exact ((hdf.comp x harg).const_mul (w t)).congr_deriv (by ring))).2

private lemma contDiffOn_hadamardInt {lo c : ℝ} (hc : lo < c) :
    ∀ n : ℕ, ∀ w f : ℝ → ℝ, ContinuousOn w (Set.Icc 0 1) →
      ContDiffOn ℝ ∞ f (Set.Ioi lo) → ContDiffOn ℝ n (hadamardInt c w f) (Set.Ioi lo) := by
  intro n
  induction n with
  | zero =>
    intro w f hw hf; change ContDiffOn ℝ 0 (hadamardInt c w f) (Set.Ioi lo); rw [contDiffOn_zero]
    exact fun x₀ hx₀ => (hadamardInt_hasDerivAt hc hw hf hx₀).continuousAt.continuousWithinAt
  | succ n ih =>
    intro w f hw hf; rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    exact ⟨fun x hx => (hadamardInt_hasDerivAt hc hw hf hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp),
      (ih (fun t => t * w t) (_root_.deriv f) (continuousOn_id.mul hw)
        (hf.deriv_of_isOpen (m := ∞) isOpen_Ioi (by simp))).congr fun x hx =>
        (hadamardInt_hasDerivAt hc hw hf hx).deriv⟩

private noncomputable def hadamardQ (c : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  hadamardInt c (fun _ => 1) (_root_.deriv f) x

private lemma hadamardQ_contDiffOn {lo c : ℝ} (hc : lo < c) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi lo)) : ContDiffOn ℝ ∞ (hadamardQ c f) (Set.Ioi lo) :=
  contDiffOn_infty.mpr fun n => contDiffOn_hadamardInt hc n (fun _ => 1) (_root_.deriv f)
    continuousOn_const (hf.deriv_of_isOpen (m := ∞) isOpen_Ioi (by simp))

private lemma sub_eq_mul_hadamardQ {lo c : ℝ} (hc : lo < c) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi lo)) {x : ℝ} (hx : lo < x) :
    f x - f c = (x - c) * hadamardQ c f x := by
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) 1, lo < c + t * (x - c) := fun t ht => by
    rw [Set.uIcc_of_le zero_le_one] at ht; rw [show c + t * (x - c) = (1 - t) * c + t * x by ring]
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]; linarith
    · calc lo = (1 - t) * lo + t * lo := by ring
        _ < (1 - t) * c + t * x := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hc.le ht1)
            (mul_lt_mul_of_pos_left hx h0)
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u => f (c + u * (x - c))) ((x - c) * _root_.deriv f (c + t * (x - c))) t := fun t ht => by
    have hdf : HasDerivAt f (_root_.deriv f (c + t * (x - c))) (c + t * (x - c)) :=
      ((hf.contDiffAt (Ioi_mem_nhds (hmem t ht))).differentiableAt (by simp)).hasDerivAt
    have harg : HasDerivAt (fun u : ℝ => c + u * (x - c)) (x - c) t := by
      simpa using (hasDerivAt_const t c).fun_add ((hasDerivAt_id t).mul_const (x - c))
    exact (hdf.comp t harg).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t => (x - c) * _root_.deriv f (c + t * (x - c))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact continuousOn_const.mul ((hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).comp
      (continuousOn_const.add (continuousOn_id.mul continuousOn_const))
      fun t ht => hmem t (by rwa [Set.uIcc_of_le zero_le_one]))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at hftc
  rw [← hftc]; unfold hadamardQ hadamardInt; rw [← intervalIntegral.integral_const_mul]
  congr 1 with t; ring

private lemma hadamardQ_self (c : ℝ) (f : ℝ → ℝ) : hadamardQ c f c = _root_.deriv f c := by
  unfold hadamardQ hadamardInt; simp

/-! ### Lemma `W.1(b)–(c)` (`(CR.16)`) for `cohnM = airyAi' / airyAi` -/

/-- **Lemma `W.1(b)`**: `|(z ∂_z)^k m(z)| ≤ C_k √z` for `z ≥ z₀`, conditional on the Bessel
ratio identity `hBesselRatio`. -/
theorem cohnM_eulerDeriv_bound
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ))) :
    ∃ z₀ ≥ 1, ∀ k : ℕ, ∃ C ≥ 0, ∀ z ≥ z₀, |eulerDeriv k cohnM z| ≤ C * Real.sqrt z := by
  obtain ⟨z₀, hz₀, hbd⟩ := besselModel_eulerDeriv_bound
  refine ⟨z₀, hz₀, fun k => ?_⟩
  obtain ⟨C, hC, h⟩ := hbd k
  refine ⟨C, hC, fun z hz => ?_⟩
  have hz_pos : 0 < z := by linarith
  rw [eulerDeriv_congr_open isOpen_Ioi (fun y hy => hBesselRatio y hy) k hz_pos]
  exact h z hz

private lemma contDiff_airyAi' : ContDiff ℝ ∞ airyAi' := by
  have heq : airyAi' = _root_.deriv airyAi := funext fun x => (deriv_airyAi x).symm
  rw [heq]
  have hAi : ContDiff ℝ ∞ airyAi := contDiff_airyAi.of_le (by simp)
  exact contDiffOn_univ.mp (hAi.contDiffOn.deriv_of_isOpen isOpen_univ (by simp))

private lemma cohnM_contDiffOn : ContDiffOn ℝ ∞ cohnM (Set.Ioi (airyZero 1)) :=
  contDiff_airyAi'.contDiffOn.div (contDiff_airyAi.of_le le_top).contDiffOn
    fun _ hz => airyAi_ne_zero_of_gt hz

/-- Smoothness of `cohnVSmooth a` on `(a₁, ∞)`, handling the removable singularity at `z = a`. -/
theorem cohnVSmooth_contDiffOn {a : ℝ} (ha : airyAi' a = 0) :
    ContDiffOn ℝ ∞ (cohnVSmooth a) (Set.Ioi (airyZero 1)) := by
  by_cases ha_gt : airyZero 1 < a
  · let g : ℝ → ℝ := hadamardQ a cohnM
    have hg_cd : ContDiffOn ℝ ∞ g (Set.Ioi (airyZero 1)) := hadamardQ_contDiffOn ha_gt cohnM_contDiffOn
    let q : ℝ → ℝ := hadamardQ a g
    have hq_cd : ContDiffOn ℝ ∞ q (Set.Ioi (airyZero 1)) := hadamardQ_contDiffOn ha_gt hg_cd
    have hma : cohnM a = 0 := by simp [cohnM, ha]
    have hga : g a = a := by
      dsimp [g]; rw [hadamardQ_self, (cohnM_hasDerivAt (airyAi_ne_zero_of_deriv_zero ha)).deriv]; simp [hma]
    have hfac1 : ∀ z > airyZero 1, cohnM z = (z - a) * g z := fun z hz => by
      have h := sub_eq_mul_hadamardQ ha_gt cohnM_contDiffOn hz; rwa [hma, sub_zero] at h
    have hfac2 : ∀ z > airyZero 1, cohnM z - a * (z - a) = (z - a) ^ 2 * q z := fun z hz => by
      have h := sub_eq_mul_hadamardQ ha_gt hg_cd hz; rw [hga] at h
      calc cohnM z - a * (z - a) = (z - a) * (g z - a) := by rw [hfac1 z hz]; ring
        _ = (z - a) ^ 2 * q z := by rw [h]; ring
    have hqa : q a = 1 / 2 := by
      have hderiv_m : ∀ z > airyZero 1, _root_.deriv cohnM z = g z + (z - a) * _root_.deriv g z := fun z hz => by
        have hev : cohnM =ᶠ[𝓝 z] (fun y => (y - a) * g y) :=
          Filter.eventually_of_mem (Ioi_mem_nhds hz) fun y hy => hfac1 y hy
        rw [hev.deriv_eq]
        have hd_lin : HasDerivAt (fun y : ℝ => y - a) 1 z := by simpa using (hasDerivAt_id z).sub_const a
        have hd_g : HasDerivAt g (_root_.deriv g z) z :=
          ((hg_cd.contDiffAt (Ioi_mem_nhds hz)).differentiableAt (by simp)).hasDerivAt
        rw [(hd_lin.fun_mul hd_g).deriv]; ring
      have hderiv2_a : _root_.deriv (_root_.deriv cohnM) a = 2 * _root_.deriv g a := by
        have hev : _root_.deriv cohnM =ᶠ[𝓝 a] (fun y => g y + (y - a) * _root_.deriv g y) :=
          Filter.eventually_of_mem (Ioi_mem_nhds ha_gt) fun y hy => hderiv_m y hy
        rw [hev.deriv_eq]
        have hd_g : HasDerivAt g (_root_.deriv g a) a :=
          ((hg_cd.contDiffAt (Ioi_mem_nhds ha_gt)).differentiableAt (by simp)).hasDerivAt
        have hd_g' : HasDerivAt (_root_.deriv g) (_root_.deriv (_root_.deriv g) a) a :=
          (((hg_cd.deriv_of_isOpen (m := ∞) isOpen_Ioi (by simp)).contDiffAt
            (Ioi_mem_nhds ha_gt)).differentiableAt (by simp)).hasDerivAt
        have hd_lin : HasDerivAt (fun y : ℝ => y - a) 1 a := by simpa using (hasDerivAt_id a).sub_const a
        rw [(hd_g.fun_add (hd_lin.fun_mul hd_g')).deriv]; ring
      have hriccati2 : _root_.deriv (_root_.deriv cohnM) a = 1 := by
        have hev : _root_.deriv cohnM =ᶠ[𝓝 a] (fun y => y - cohnM y ^ 2) :=
          Filter.eventually_of_mem (Ioi_mem_nhds ha_gt) fun y hy =>
            (cohnM_hasDerivAt (airyAi_ne_zero_of_gt hy)).deriv
        rw [hev.deriv_eq]
        have hd_m : HasDerivAt cohnM (_root_.deriv cohnM a) a :=
          ((cohnM_contDiffOn.contDiffAt (Ioi_mem_nhds ha_gt)).differentiableAt (by simp)).hasDerivAt
        have hsub : HasDerivAt (fun y : ℝ => y - cohnM y ^ 2) (1 - 2 * cohnM a * _root_.deriv cohnM a) a :=
          ((hasDerivAt_id a).fun_sub (hd_m.fun_pow 2)).congr_deriv (by ring)
        rw [hsub.deriv, hma]; ring
      dsimp [q]; rw [hadamardQ_self]; linarith
    refine hq_cd.congr fun z hz => ?_
    by_cases hza : z = a
    · subst hza; simp [cohnVSmooth, hqa]
    · have hne : (z - a) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hza)
      simp only [cohnVSmooth, hza, ↓reduceIte, cohnV]; rw [hfac2 z hz]; field_simp
  · have hlin : ContDiffOn ℝ ∞ (fun z : ℝ => a * (z - a)) (Set.Ioi (airyZero 1)) :=
      (contDiff_const.mul (contDiff_id.sub contDiff_const)).contDiffOn
    have hsq : ContDiffOn ℝ ∞ (fun z : ℝ => (z - a) ^ 2) (Set.Ioi (airyZero 1)) :=
      ((contDiff_id.sub contDiff_const).pow 2).contDiffOn
    refine ((cohnM_contDiffOn.sub hlin).div hsq fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr
      (ne_of_gt (lt_of_le_of_lt (not_lt.mp ha_gt) (Set.mem_Ioi.mp hz))))).congr fun z hz => ?_
    have hza : z ≠ a := ne_of_gt (lt_of_le_of_lt (not_lt.mp ha_gt) (Set.mem_Ioi.mp hz))
    simp [cohnVSmooth, cohnV, hza]

private lemma cardinal_CR16_smooth_open {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a) :
    ∃ ε > 0, ContDiffOn ℝ ∞ (cohnCR16F a) (Set.Ioi (-ε)) := by
  let a₁ : ℝ := airyZero 1
  let qAi : ℝ → ℝ := hadamardQ a₁ airyAi
  have hqAi_cd : ContDiffOn ℝ ∞ qAi (Set.Ioi (a₁ - 1)) :=
    hadamardQ_contDiffOn (by linarith) (contDiff_airyAi.of_le le_top).contDiffOn
  have hqAi_self : qAi a₁ = airyAi' a₁ := by dsimp [qAi]; rw [hadamardQ_self, deriv_airyAi]
  have hAi'0 : airyAi' a₁ ≠ 0 := fun h => airyAi_ne_zero_of_deriv_zero h (airyAi_airyZero 1)
  have hqAi_cont : ContinuousAt (fun t : ℝ => qAi (a₁ + t)) 0 := by
    have hca : ContinuousAt qAi (a₁ + 0) := by
      rw [add_zero]
      exact (hqAi_cd.continuousOn.continuousWithinAt (by simp)).continuousAt (Ioi_mem_nhds (by linarith))
    exact hca.comp (continuousAt_const.fun_add continuousAt_id)
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp
    (hqAi_cont.eventually_ne (by simpa [hqAi_self] using hAi'0))
  set ε : ℝ := min (1 / 2) (min δ (a - a₁) / 2)
  have hε_pos : 0 < ε := lt_min (by norm_num) (half_pos (lt_min hδ_pos (sub_pos.mpr ha1)))
  have hε_δ : ε < δ := by linarith [min_le_right (1 / 2) (min δ (a - a₁) / 2), min_le_left δ (a - a₁)]
  have hε_aa1 : ε < a - a₁ := by linarith [min_le_right (1 / 2) (min δ (a - a₁) / 2), min_le_right δ (a - a₁)]
  let F_loc : ℝ → ℝ := fun t => (airyAi' (a₁ + t) / qAi (a₁ + t) - a * t * (a₁ + t - a)) / (a₁ + t - a) ^ 2
  have hF_loc_cd : ContDiffOn ℝ ∞ F_loc (Set.Ioo (-ε) ε) := by
    have hshift_cd : ContDiffOn ℝ ∞ (fun t : ℝ => qAi (a₁ + t)) (Set.Ioo (-ε) ε) :=
      hqAi_cd.comp (contDiff_const.add contDiff_id).contDiffOn fun t ht => by
        rw [Set.mem_Ioi]; linarith [ht.1, min_le_left (1 / 2) (min δ (a - a₁) / 2)]
    have hq_ne : ∀ t ∈ Set.Ioo (-ε) ε, qAi (a₁ + t) ≠ 0 := fun t ht =>
      hδ_ball (y := t) (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact (((contDiff_airyAi'.comp (contDiff_const.add contDiff_id)).contDiffOn.div hshift_cd hq_ne).sub
      ((contDiff_const.mul contDiff_id).mul ((contDiff_const.add contDiff_id).sub contDiff_const)).contDiffOn).div
      (((contDiff_const.add contDiff_id).sub contDiff_const).pow 2).contDiffOn
      fun t ht => pow_ne_zero 2 (by dsimp; linarith [ht.2])
  have hF_eq_loc : Set.EqOn (cohnCR16F a) F_loc (Set.Ioo (-ε) ε) := fun t ht => by
    have hta : a₁ + t ≠ a := by linarith [ht.2]
    by_cases ht0 : t = 0
    · subst ht0; simp only [cohnCR16F, ↓reduceIte, F_loc, add_zero, mul_zero, hqAi_self]
      dsimp [a₁] at hAi'0 ⊢; field_simp [hAi'0]; ring
    · have hAi_fac : airyAi (a₁ + t) = t * qAi (a₁ + t) := by
        have h := sub_eq_mul_hadamardQ (lo := a₁ - 1) (c := a₁) (by linarith)
          (contDiff_airyAi.of_le le_top).contDiffOn (x := a₁ + t)
          (by linarith [ht.1, min_le_left (1 / 2) (min δ (a - a₁) / 2)])
        rwa [airyAi_airyZero 1, sub_zero, add_sub_cancel_left] at h
      have hq_ne : qAi (a₁ + t) ≠ 0 := hδ_ball (y := t) (by
        rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      have htm : t * cohnM (a₁ + t) = airyAi' (a₁ + t) / qAi (a₁ + t) := by
        unfold cohnM; rw [hAi_fac]; field_simp [ht0, hq_ne]
      have hta' : airyZero 1 + t ≠ a := hta
      simp only [cohnCR16F, ht0, ↓reduceIte, cohnVSmooth, hta', cohnV, F_loc]
      dsimp [a₁] at htm ⊢; rw [← htm]; field_simp [sub_ne_zero.mpr hta']
  have hF_cd_pos : ContDiffOn ℝ ∞ (cohnCR16F a) (Set.Ioi 0) := by
    have hshift : ContDiffOn ℝ ∞ (fun t : ℝ => airyZero 1 + t) (Set.Ioi 0) :=
      (contDiff_const.add contDiff_id).contDiffOn
    exact (contDiffOn_id.mul ((cohnVSmooth_contDiffOn ha).comp hshift fun t ht => by
      rw [Set.mem_Ioi] at ht ⊢; linarith)).congr fun t ht => by
        simp [cohnCR16F, ne_of_gt (Set.mem_Ioi.mp ht)]
  have hF_cd_loc : ContDiffOn ℝ ∞ (cohnCR16F a) (Set.Ioo (-ε) ε) := hF_loc_cd.congr hF_eq_loc
  refine ⟨ε, hε_pos, fun t ht => ?_⟩
  have ht' : -ε < t := ht
  rcases lt_trichotomy t 0 with ht_neg | rfl | ht_pos
  · exact (hF_cd_loc.contDiffAt (Ioo_mem_nhds ht' (by linarith))).contDiffWithinAt
  · exact (hF_cd_loc.contDiffAt (Ioo_mem_nhds (by linarith) hε_pos)).contDiffWithinAt
  · exact (hF_cd_pos.contDiffAt (Ioi_mem_nhds ht_pos)).contDiffWithinAt

/-- Smoothness of `cohnCR16F a` on `[0, ∞)` (extending `t ↦ t v(a₁ + t)` across `t = 0`). -/
theorem cardinal_CR16_smooth {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a) :
    ContDiffOn ℝ ∞ (cohnCR16F a) (Set.Ici 0) := by
  obtain ⟨ε, hε, hcd⟩ := cardinal_CR16_smooth_open ha ha1
  exact hcd.mono fun t ht => by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.mp ht]

/-- **Lemma `W.1(c)` / `(CR.16)`**: `F(t) = t v(a₁ + t)` satisfies
`sup_{t > 0} |(t ∂_t)^k F(t)| < ∞` for all `k : ℕ`, and `F(t) = -a + O(t^{-1/2})` as `t → ∞`. -/
theorem cardinal_CR16 {a : ℝ} (ha : airyAi' a = 0) (ha1 : airyZero 1 < a) (_ha0 : a < 0)
    (hBesselRatio : ∀ z > 0, cohnM z = -Real.sqrt z * besselR ((2 / 3 : ℝ) * z ^ (3 / 2 : ℝ))) :
    let F : ℝ → ℝ := fun t => t * cohnVSmooth a (airyZero 1 + t)
    (∀ k : ℕ, ∃ C ≥ 0, ∀ t > 0, |eulerDeriv k F t| ≤ C) ∧
      ∃ C ≥ 0, ∀ t ≥ 1, |F t + a| ≤ C * t ^ (-(1 / 2 : ℝ)) := by
  intro F
  set a₁ : ℝ := airyZero 1; set d : ℝ := a₁ - a
  have ha₁_neg : a₁ < 0 := airyZero_neg 1
  obtain ⟨z₀, _, hM_ed⟩ := cohnM_eulerDeriv_bound hBesselRatio
  set T : ℝ := max 1 (max (z₀ - a₁) (max (2 * |d|) (2 * |a₁|)))
  have hT_ge1 : 1 ≤ T := le_max_left _ _
  have hT_z0 : z₀ ≤ a₁ + T := by
    have h1 : z₀ - a₁ ≤ max (z₀ - a₁) (max (2 * |d|) (2 * |a₁|)) := le_max_left _ _
    have h2 : max (z₀ - a₁) (max (2 * |d|) (2 * |a₁|)) ≤ T := le_max_right _ _
    linarith
  have hT_d : 2 * |d| ≤ T := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hT_a1 : 2 * |a₁| ≤ T := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hT_pos : 0 < T := by linarith
  let U_t : Set ℝ := Set.Ioi (T - 1 / 2)
  have hU_t_open : IsOpen U_t := isOpen_Ioi
  have hU_t_sub : Set.Ici T ⊆ U_t := fun t ht => by rw [Set.mem_Ioi]; linarith [Set.mem_Ici.mp ht]
  have hU_t_td : ∀ t ∈ U_t, 0 < t + d := fun t ht => by
    rw [Set.mem_Ioi] at ht; linarith [(abs_le.mp (show |d| ≤ T / 2 by linarith)).1]
  have hU_t_ta1 : ∀ t ∈ U_t, 0 < t + a₁ := fun t ht => by
    rw [Set.mem_Ioi] at ht; linarith [(abs_le.mp (show |a₁| ≤ T / 2 by linarith)).1]
  have hU_t_z0 : ∀ t ∈ U_t, z₀ - 1 < a₁ + t := fun t ht => by rw [Set.mem_Ioi] at ht; linarith
  have hinv_shift_sym : ∀ c : ℝ, 2 * |c| ≤ T → IsSymbolOn T 0 (fun t : ℝ => (1 + c * t⁻¹)⁻¹) := fun c hc => by
    have hct0 : IsSymbolOn T 0 (fun t : ℝ => c * t⁻¹) :=
      ((IsSymbolOn.inv hT_pos).const_mul c).mono_exp hT_pos zero_le_one
    have hG_cd : ContDiffOn ℝ ∞ (fun w : ℝ => (1 + w)⁻¹) (Set.Ioo (-(3 / 4 : ℝ)) (3 / 4)) :=
      ((contDiff_const.add contDiff_id).contDiffOn).inv fun w hw => by dsimp; linarith [hw.1]
    have hrange : ∀ t ≥ T, c * t⁻¹ ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := fun t ht =>
      abs_le.mp (by rw [abs_mul, abs_inv, abs_of_pos (by linarith : 0 < t),
        ← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < t)]; linarith)
    exact ((hct0.comp_sub_zero hT_pos le_rfl (a := -(3 / 4)) (a' := -(1 / 2)) (b' := 1 / 2) (b := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hrange hG_cd).add_same
      (IsSymbolOn.const hT_pos le_rfl 1)).congr fun t _ => by simp
  have htd_inv_sym : IsSymbolOn T 1 (fun t : ℝ => (t + d)⁻¹) := by
    have hmul := (IsSymbolOn.inv hT_pos).mul hT_pos (hinv_shift_sym d hT_d)
    rw [add_zero] at hmul
    refine hmul.congr fun t ht => ?_
    rw [Set.mem_Ici] at ht
    have ht0 : t ≠ 0 := by linarith
    have htd0 : t + d ≠ 0 := (hU_t_td t (hU_t_sub ht)).ne'
    field_simp
  have hg_sym : IsSymbolOn T 1 (fun t : ℝ => t / (t + d) ^ 2) := by
    have hmul := htd_inv_sym.mul hT_pos (hinv_shift_sym d hT_d)
    rw [add_zero] at hmul
    refine hmul.congr fun t ht => ?_
    rw [Set.mem_Ici] at ht
    have ht0 : t ≠ 0 := by linarith
    have htd0 : t + d ≠ 0 := (hU_t_td t (hU_t_sub ht)).ne'
    field_simp
  have hpsi_sym : IsSymbolOn T 0 (fun t : ℝ => t / (t + a₁)) := by
    refine (hinv_shift_sym a₁ hT_a1).congr fun t ht => ?_
    rw [Set.mem_Ici] at ht
    have ht0 : t ≠ 0 := by linarith
    have hta0 : t + a₁ ≠ 0 := (hU_t_ta1 t (hU_t_sub ht)).ne'
    field_simp
  have hpsi_cd : ContDiffOn ℝ ∞ (fun t : ℝ => t / (t + a₁)) U_t :=
    contDiffOn_id.div (contDiff_id.add contDiff_const).contDiffOn fun t ht => (hU_t_ta1 t ht).ne'
  have hg_cd : ContDiffOn ℝ ∞ (fun t : ℝ => t / (t + d) ^ 2) U_t :=
    contDiffOn_id.div ((contDiff_id.add contDiff_const).pow 2).contDiffOn fun t ht =>
      pow_ne_zero 2 (hU_t_td t ht).ne'
  have hshift_ed : ∀ j : ℕ, ∀ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ (Set.Ioi (z₀ - 1)) →
      (∀ m : ℕ, ∃ D ≥ 0, ∀ z ≥ z₀, |eulerDeriv m φ z| ≤ D * Real.sqrt z) →
      ∃ E ≥ 0, ∀ t ≥ T, |eulerDeriv j (fun s => φ (a₁ + s)) t| ≤ E * Real.sqrt (a₁ + t) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro φ hφ_cd hφbd
      cases j with
      | zero => obtain ⟨D, hD, hbd⟩ := hφbd 0; exact ⟨D, hD, fun t ht => hbd (a₁ + t) (by linarith)⟩
      | succ j =>
        have hop_cd := eulerDerivOp_contDiffOn isOpen_Ioi hφ_cd
        have hop_bd : ∀ m : ℕ, ∃ D ≥ 0, ∀ z ≥ z₀, |eulerDeriv m (eulerDerivOp φ) z| ≤ D * Real.sqrt z :=
          fun m => by simpa only [eulerDeriv_succ'] using hφbd (m + 1)
        have heq_op : Set.EqOn (eulerDerivOp (fun s => φ (a₁ + s)))
            (fun s => (s / (s + a₁)) * eulerDerivOp φ (a₁ + s)) U_t := fun s hs => by
          have h1 : HasDerivAt (fun u : ℝ => a₁ + u) 1 s := by simpa using (hasDerivAt_id s).const_add a₁
          have h2 : HasDerivAt φ (_root_.deriv φ (a₁ + s)) (a₁ + s) :=
            ((hφ_cd.contDiffAt (Ioi_mem_nhds (hU_t_z0 s hs))).differentiableAt (by simp)).hasDerivAt
          have hcomp : HasDerivAt (fun u => φ (a₁ + u)) (_root_.deriv φ (a₁ + s) * 1) s := h2.comp s h1
          have hta0 : s + a₁ ≠ 0 := (hU_t_ta1 s hs).ne'
          unfold eulerDerivOp; rw [hcomp.deriv, mul_one]; field_simp [hta0]; ring
        have hcomp_op_cd : ContDiffOn ℝ ∞ (fun s => eulerDerivOp φ (a₁ + s)) U_t :=
          hop_cd.comp (contDiff_const.add contDiff_id).contDiffOn fun s hs => hU_t_z0 s hs
        choose B hB_nn hBbd using fun i => by
          simpa using (isSymbolOn_eulerDeriv_iter hT_pos hU_t_open hU_t_sub hpsi_cd hpsi_sym i).abs_le
        have hE' : ∀ i : ℕ, ∃ E ≥ 0, ∀ t ≥ T,
            i ≤ j → |eulerDeriv i (fun s => eulerDerivOp φ (a₁ + s)) t| ≤ E * Real.sqrt (a₁ + t) := fun i => by
          by_cases hij : i ≤ j
          · obtain ⟨E, hE, hbd⟩ := ih i (by omega) (eulerDerivOp φ) hop_cd hop_bd
            exact ⟨E, hE, fun t ht _ => hbd t ht⟩
          · exact ⟨0, le_rfl, fun _ _ h => absurd h hij⟩
        choose E hE_nn hEbd using hE'
        refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * E (j - i),
          Finset.sum_nonneg fun i _ => by positivity [hB_nn i, hE_nn (j - i)], fun t ht => ?_⟩
        rw [eulerDeriv_succ', eulerDeriv_congr_open hU_t_open heq_op j (hU_t_sub ht)]
        have hmul := eulerDeriv_mul_bound hU_t_open hpsi_cd hcomp_op_cd (k := j) (x := t) (hU_t_sub ht)
          (A := B) (B := E) (w₁ := 1) (w₂ := Real.sqrt (a₁ + t))
          (fun i _ => by simpa using hBbd i t ht) (fun i hi => hEbd i t ht hi)
        simpa only [one_mul] using hmul
  let F₁ : ℝ → ℝ := fun t => (t / (t + d) ^ 2) * cohnM (a₁ + t)
  let F₂ : ℝ → ℝ := fun t => -a * (t / (t + d))
  have hM_cd_z0 : ContDiffOn ℝ ∞ cohnM (Set.Ioi (z₀ - 1)) :=
    cohnM_contDiffOn.mono fun z hz => by rw [Set.mem_Ioi] at hz ⊢; linarith
  have hM_shift_cd : ContDiffOn ℝ ∞ (fun s => cohnM (a₁ + s)) U_t :=
    hM_cd_z0.comp (contDiff_const.add contDiff_id).contDiffOn fun s hs => hU_t_z0 s hs
  have hF₁_cd : ContDiffOn ℝ ∞ F₁ U_t := hg_cd.mul hM_shift_cd
  have hF₂_cd : ContDiffOn ℝ ∞ F₂ U_t :=
    contDiffOn_const.mul (contDiffOn_id.div (contDiff_id.add contDiff_const).contDiffOn fun t ht => (hU_t_td t ht).ne')
  have hF_eq_sum : Set.EqOn F (fun t => F₁ t + F₂ t) U_t := fun t ht => by
    have hta : airyZero 1 + t ≠ a := fun h => (hU_t_td t ht).ne' (by dsimp [d, a₁]; linarith)
    dsimp [F, F₁, F₂, cohnVSmooth, cohnV]; simp only [hta, ↓reduceIte]
    rw [show a₁ + t - a = t + d by dsimp [d]; ring]; dsimp [a₁]
    field_simp [(hU_t_td t ht).ne']; ring
  have hF₁_bound : ∀ k : ℕ, ∃ K ≥ 0, ∀ t ≥ T, |eulerDeriv k F₁ t| ≤ K * t ^ (-(1 / 2 : ℝ)) := fun k => by
    choose Cg hCg_nn hCg using fun i =>
      (isSymbolOn_eulerDeriv_iter hT_pos hU_t_open hU_t_sub hg_cd hg_sym i).abs_le
    choose Em hEm_nn hEm using fun i => hshift_ed i cohnM hM_cd_z0 hM_ed
    refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cg i * Em (k - i),
      Finset.sum_nonneg fun i _ => by positivity [hCg_nn i, hEm_nn (k - i)], fun t ht => ?_⟩
    have ht0 : 0 < t := by linarith
    have hsqrt_le : Real.sqrt (a₁ + t) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
    have hmul := eulerDeriv_mul_bound hU_t_open hg_cd hM_shift_cd (k := k) (x := t) (hU_t_sub ht)
      (A := Cg) (B := Em) (w₁ := t ^ (-1 : ℝ)) (w₂ := Real.sqrt t)
      (fun i _ => hCg i t ht)
      (fun i _ => (hEm i t ht).trans (mul_le_mul_of_nonneg_left hsqrt_le (hEm_nn i)))
    have hrpow_mul : t ^ (-1 : ℝ) * Real.sqrt t = t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; norm_num
    rwa [hrpow_mul] at hmul
  have hF₂_plus_sym : IsSymbolOn T 1 (fun t : ℝ => F₂ t + a) := by
    refine (htd_inv_sym.const_mul (a * d)).congr fun t ht => ?_
    rw [Set.mem_Ici] at ht
    have htd0 := (hU_t_td t (hU_t_sub ht)).ne'
    dsimp [F₂]; field_simp; ring
  obtain ⟨C₂_0, hC₂_0_nn, hC₂_0⟩ := hF₂_plus_sym.abs_le
  obtain ⟨ε, hε_pos, hF₀_cd⟩ := cardinal_CR16_smooth_open ha ha1
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((eulerDeriv_contDiffOn isOpen_Ioi hF₀_cd k).continuousOn.mono fun t ht => by
        have ht0 : 0 ≤ t := ht.1; rw [Set.mem_Ioi]; linarith)
    obtain ⟨K₁, hK₁_nn, hK₁⟩ := hF₁_bound k
    have hF₂_ed_bound : ∃ M₂ ≥ 0, ∀ t ≥ T, |eulerDeriv k F₂ t| ≤ M₂ := by
      cases k with
      | zero =>
        refine ⟨|a| + C₂_0 * T ^ (-1 : ℝ), by positivity, fun t ht => ?_⟩
        have hpow : t ^ (-1 : ℝ) ≤ T ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos hT_pos ht (by norm_num)
        calc |eulerDeriv 0 F₂ t| = |(F₂ t + a) - a| := by simp [eulerDeriv]
          _ ≤ |F₂ t + a| + |a| := abs_sub _ _
          _ ≤ C₂_0 * t ^ (-1 : ℝ) + |a| := by linarith [hC₂_0 t ht]
          _ ≤ C₂_0 * T ^ (-1 : ℝ) + |a| := by gcongr
          _ = |a| + C₂_0 * T ^ (-1 : ℝ) := by ring
      | succ k' =>
        obtain ⟨M₂, hM₂_nn, hM₂⟩ := (isSymbolOn_eulerDeriv_iter hT_pos hU_t_open hU_t_sub
          (hF₂_cd.add contDiffOn_const) hF₂_plus_sym (k' + 1)).abs_le
        refine ⟨M₂ * T ^ (-1 : ℝ), by positivity, fun t ht => ?_⟩
        have heq_deriv : Set.EqOn (eulerDerivOp F₂) (eulerDerivOp (fun s => F₂ s + a)) U_t := fun s hs => by
          have hd : HasDerivAt F₂ (_root_.deriv F₂ s) s :=
            ((hF₂_cd.contDiffAt (Ioi_mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
          unfold eulerDerivOp; rw [(hd.add_const a).deriv]
        rw [eulerDeriv_succ', eulerDeriv_congr_open hU_t_open heq_deriv k' (hU_t_sub ht)]
        exact (hM₂ t ht).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hT_pos ht (by norm_num)) hM₂_nn)
    obtain ⟨M₂, _, hM₂⟩ := hF₂_ed_bound
    refine ⟨max (max M₁ 0) (K₁ * T ^ (-(1 / 2 : ℝ)) + M₂),
      le_trans (le_max_right _ _) (le_max_left _ _), fun t ht => ?_⟩
    rcases le_or_gt t T with htT | hTt
    · have heq_pos : Set.EqOn F (cohnCR16F a) (Set.Ioi 0) := fun s hs => by
        simp [cohnCR16F, F, ne_of_gt (Set.mem_Ioi.mp hs)]
      rw [eulerDeriv_congr_open isOpen_Ioi heq_pos k ht]
      exact (hM₁ t ⟨ht.le, htT⟩).trans (le_trans (le_max_left _ _) (le_max_left _ _))
    · have htU : t ∈ U_t := hU_t_sub hTt.le
      rw [eulerDeriv_congr_open hU_t_open hF_eq_sum k htU, eulerDeriv_add_open hU_t_open hF₁_cd hF₂_cd k t htU]
      have h1 := (hK₁ t hTt.le).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hT_pos hTt.le (by norm_num)) hK₁_nn)
      exact (abs_add_le _ _).trans ((add_le_add h1 (hM₂ t hTt.le)).trans (le_max_right _ _))
  · obtain ⟨M_mid, hM_mid⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hF₀_cd.continuousOn.mono fun t ht => by rw [Set.mem_Ioi]; linarith [ht.1]).add continuousOn_const :
        ContinuousOn (fun t => cohnCR16F a t + a) (Set.Icc 1 T))
    obtain ⟨K₀, _, hK₀⟩ := hF₁_bound 0
    refine ⟨max (max M_mid 0 * Real.sqrt T) (K₀ + C₂_0),
      le_trans (by positivity) (le_max_right _ _), fun t ht1 => ?_⟩
    have ht_pos : 0 < t := by linarith
    rcases le_or_gt t T with htT | hTt
    · have heq : F t = cohnCR16F a t := by simp [cohnCR16F, F, ht_pos.ne']
      rw [heq]
      have h1 : |cohnCR16F a t + a| ≤ max M_mid 0 := (hM_mid t ⟨ht1, htT⟩).trans (le_max_left _ _)
      have h2 : 1 ≤ Real.sqrt T * t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        calc (1 : ℝ) = t ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
          _ ≤ T ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht_pos.le htT (by norm_num))
                (Real.rpow_nonneg ht_pos.le _)
      calc |cohnCR16F a t + a| ≤ max M_mid 0 * 1 := by linarith
        _ ≤ max M_mid 0 * (Real.sqrt T * t ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
        _ = (max M_mid 0 * Real.sqrt T) * t ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ max (max M_mid 0 * Real.sqrt T) (K₀ + C₂_0) * t ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht_pos.le _)
    · rw [hF_eq_sum (hU_t_sub hTt.le)]
      have h1 : |F₁ t| ≤ K₀ * t ^ (-(1 / 2 : ℝ)) := by simpa [eulerDeriv] using hK₀ t hTt.le
      have h2 : |F₂ t + a| ≤ C₂_0 * t ^ (-(1 / 2 : ℝ)) := (hC₂_0 t hTt.le).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)) hC₂_0_nn)
      calc |F₁ t + F₂ t + a| = |F₁ t + (F₂ t + a)| := by rw [add_assoc]
        _ ≤ |F₁ t| + |F₂ t + a| := abs_add_le _ _
        _ ≤ K₀ * t ^ (-(1 / 2 : ℝ)) + C₂_0 * t ^ (-(1 / 2 : ℝ)) := add_le_add h1 h2
        _ = (K₀ + C₂_0) * t ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ max (max M_mid 0 * Real.sqrt T) (K₀ + C₂_0) * t ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht_pos.le _)

/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.abs_iteratedDeriv_besselJ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.abs_iteratedDeriv_besselJ_le

/-- info: 'FormalResearch.CohnElkies.besselP_isSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.besselP_isSymbol

/-- info: 'FormalResearch.CohnElkies.tendsto_besselP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.tendsto_besselP

/-- info: 'FormalResearch.CohnElkies.besselR_isSymbolOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.besselR_isSymbolOn

/-- info: 'FormalResearch.CohnElkies.besselModel_eulerDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.besselModel_eulerDeriv_bound

/-- info: 'FormalResearch.CohnElkies.cohnM_eulerDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnM_eulerDeriv_bound

/-- info: 'FormalResearch.CohnElkies.cardinal_CR16_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_CR16_smooth

/-- info: 'FormalResearch.CohnElkies.cardinal_CR16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cardinal_CR16

end FormalResearch.CohnElkies
