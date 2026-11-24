module

public import Mathlib
public import FormalResearch.SignUncertainty.ConvSourceWeight

/-!
# Derivative bounds for the long-range weight `w_h` (M6, Lemma `O.12`, `ceo:conv.4`)

For `1/2 < p < 1`, `h > 0` and `y > 0`, the weight `w_h(y) = η(y) ϱ(h y) y^{-3/2}` of
`ConvSourceDefs` satisfies, for every `r`, with a constant depending only on `p` and `r`:
`|∂^r w_h(y)| ≤ C_r y^{-3/2-r}` (`convW_deriv_bound`, stated for `y ≥ 1`).

Route. A function `f` is *good with exponent `a` and constants `C`* on `(0, ∞)` when it is
smooth there and `|∂^k f(t)| ≤ C_k t^{-a-k}` for all `k` and `t > 0`. Such functions are closed
under pointwise products (Leibniz rule, `iteratedDeriv_mul`), under composition with the affine
maps `t ↦ c t + d` (`convWd_affine`), and the building blocks are:
the powers `t^s` (exponent `-s`), `(t + 1)^{-p}` (exponent `p`), the cutoff `η` (exponent `0`),
and `ϱ(t) = t^p (t+1)^{-p}` (exponent `0`), which gives `ϱ(h y)` with the same constants for all
`h > 0`. Derivatives are taken only on the open set `(0, ∞)`, where `w_h` coincides with the
product of the building blocks.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- Smoothness of order `⊤` gives smoothness of any finite order `k`. -/
lemma convWd_cdk {f : ℝ → ℝ} {t : ℝ} (k : ℕ) (h : ContDiffAt ℝ (⊤ : ℕ∞) f t) :
    ContDiffAt ℝ (k : WithTop ℕ∞) f t :=
  h.of_le (by exact_mod_cast le_top)

/-- Derivatives of a power: `∂^k (t^s) = c t^{s-k}` on `(0, ∞)`. -/
lemma convWd_pow_formula : ∀ (k : ℕ) (s : ℝ), ∃ c : ℝ, ∀ t : ℝ, 0 < t →
    iteratedDeriv k (fun t => t ^ s) t = c * t ^ (s - k) := by
  intro k
  induction k with
  | zero => intro s; exact ⟨1, fun t ht => by simp⟩
  | succ k ih =>
    intro s
    obtain ⟨c, hc⟩ := ih (s - 1)
    refine ⟨s * c, fun t ht => ?_⟩
    have hd : Set.EqOn (deriv (fun t : ℝ => t ^ s)) (fun t => s * t ^ (s - 1)) (Ioi 0) :=
      fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).deriv
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ (s - 1)) t :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)
    have e1 : iteratedDeriv k (deriv (fun t : ℝ => t ^ s)) t
        = iteratedDeriv k (fun t => s * t ^ (s - 1)) t :=
      (Set.EqOn.iteratedDeriv_of_isOpen hd isOpen_Ioi k) ht
    have e2 : iteratedDeriv k (fun t => s * t ^ (s - 1)) t
        = s * iteratedDeriv k (fun t => t ^ (s - 1)) t :=
      iteratedDeriv_const_mul s (convWd_cdk k hcd)
    rw [iteratedDeriv_succ', e1, e2, hc t ht]
    rw [show s - ((k + 1 : ℕ) : ℝ) = s - 1 - k by push_cast; ring]
    ring

/-- Affine change of variables: `∂^k [f(c t + d)] = c^k (∂^k f)(c t + d)`, for `f` smooth on an
open set `U` and `c t + d ∈ U`. -/
lemma convWd_affine (U : Set ℝ) (hU : IsOpen U) (c d : ℝ) (k : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (t : ℝ) (ht : c * t + d ∈ U) :
    iteratedDeriv k (fun s => f (c * s + d)) t = c ^ k * iteratedDeriv k f (c * t + d) := by
  induction k generalizing f t with
  | zero => simp
  | succ k ih =>
    have hV : IsOpen {s : ℝ | c * s + d ∈ U} := hU.preimage (by fun_prop)
    have hd : Set.EqOn (deriv (fun s => f (c * s + d))) (fun s => c * deriv f (c * s + d))
        {s : ℝ | c * s + d ∈ U} := by
      intro s hs
      have hfd : DifferentiableAt ℝ f (c * s + d) :=
        (hf.contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
      have h1 : HasDerivAt (fun s : ℝ => c * s + d) c s := by
        simpa using ((hasDerivAt_id s).const_mul c).add_const d
      have h2 := hfd.hasDerivAt.comp s h1
      rw [show (fun s => f (c * s + d)) = f ∘ (fun s => c * s + d) from rfl, h2.deriv]
      ring
    have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (deriv f) U := hf.deriv_of_isOpen hU (by simp)
    have hdcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => deriv f (c * s + d)) t :=
      (hdf.contDiffAt (hU.mem_nhds ht)).comp t
        ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
    have e1 : iteratedDeriv k (deriv (fun s => f (c * s + d))) t
        = iteratedDeriv k (fun s => c * deriv f (c * s + d)) t :=
      (Set.EqOn.iteratedDeriv_of_isOpen hd hV k) ht
    have e2 : iteratedDeriv k (fun s => c * deriv f (c * s + d)) t
        = c * iteratedDeriv k (fun s => deriv f (c * s + d)) t :=
      iteratedDeriv_const_mul c (convWd_cdk k hdcd)
    rw [iteratedDeriv_succ', e1, e2, ih (deriv f) hdf t ht, iteratedDeriv_succ' (f := f)]
    ring

/-- A function is good with exponent `a` and constants `C` on `(0, ∞)`. -/
def convWdGood (a : ℝ) (f : ℝ → ℝ) (C : ℕ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) f (Ioi 0) ∧
    ∀ (k : ℕ) (t : ℝ), 0 < t → |iteratedDeriv k f t| ≤ C k * t ^ (-a - k)

/-- The constants of a product: the Leibniz sum. -/
def convWdMulSeq (Cf Cg : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf i * Cg (k - i)

lemma convWd_contDiffAt {a : ℝ} {f : ℝ → ℝ} {C : ℕ → ℝ} (h : convWdGood a f C) {t : ℝ}
    (ht : 0 < t) : ContDiffAt ℝ (⊤ : ℕ∞) f t :=
  h.1.contDiffAt (isOpen_Ioi.mem_nhds ht)

/-- Leibniz rule for good functions. -/
lemma convWd_mul {a b : ℝ} {f g : ℝ → ℝ} {Cf Cg : ℕ → ℝ} (hf : convWdGood a f Cf)
    (hg : convWdGood b g Cg) : convWdGood (a + b) (fun t => f t * g t) (convWdMulSeq Cf Cg) := by
  refine ⟨hf.1.mul hg.1, fun k t ht => ?_⟩
  rw [iteratedDeriv_fun_mul (convWd_cdk k (convWd_contDiffAt hf ht)) (convWd_cdk k (convWd_contDiffAt hg ht))]
  unfold convWdMulSeq
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hf' := hf.2 i t ht
  have hg' := hg.2 (k - i) t ht
  have hcast : ((k - i : ℕ) : ℝ) = (k : ℝ) - i := by rw [Nat.cast_sub hik]
  have hsum : (-a - (i : ℝ)) + (-b - ((k - i : ℕ) : ℝ)) = -(a + b) - (k : ℝ) := by
    rw [hcast]; ring
  have hA : 0 ≤ Cf i * t ^ (-a - (i : ℝ)) := (abs_nonneg _).trans hf'
  have hc0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_mul, Nat.abs_cast]
  calc (k.choose i : ℝ) * |iteratedDeriv i f t| * |iteratedDeriv (k - i) g t|
      = (k.choose i : ℝ) * (|iteratedDeriv i f t| * |iteratedDeriv (k - i) g t|) := by ring
    _ ≤ (k.choose i : ℝ) * ((Cf i * t ^ (-a - (i : ℝ))) * (Cg (k - i) * t ^ (-b - ((k - i : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hf' hg' (abs_nonneg _) hA) hc0
    _ = (k.choose i : ℝ) * Cf i * Cg (k - i) * t ^ (-(a + b) - (k : ℝ)) := by
        rw [← hsum, Real.rpow_add ht]; ring

/-- Transport along an equality of functions on `(0, ∞)` and of exponents. -/
lemma convWd_congr {a b : ℝ} {f g : ℝ → ℝ} {C : ℕ → ℝ} (hf : convWdGood a f C)
    (hfg : Set.EqOn f g (Ioi 0)) (hab : a = b) : convWdGood b g C := by
  subst hab
  refine ⟨hf.1.congr hfg.symm, fun k t ht => ?_⟩
  have e : iteratedDeriv k f t = iteratedDeriv k g t :=
    (Set.EqOn.iteratedDeriv_of_isOpen hfg isOpen_Ioi k) ht
  rw [← e]
  exact hf.2 k t ht

/-- Powers are good, with exponent `-s`. -/
lemma convWd_pow (s : ℝ) : ∃ C : ℕ → ℝ, convWdGood (-s) (fun t => t ^ s) C := by
  have hf : ∀ k : ℕ, ∃ c : ℝ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k (fun t => t ^ s) t = c * t ^ (s - k) := fun k => convWd_pow_formula k s
  choose c hc using hf
  refine ⟨fun k => |c k|, fun t ht => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).contDiffWithinAt,
    fun k t ht => ?_⟩
  rw [hc k t ht, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), neg_neg]

/-- `(t + 1)^{-p}` is good with exponent `p`, for `p ≥ 0`. -/
lemma convWd_shift (p : ℝ) (hp : 0 ≤ p) : ∃ C : ℕ → ℝ, convWdGood p (fun t => (t + 1) ^ (-p)) C := by
  have hf : ∀ k : ℕ, ∃ c : ℝ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k (fun t => t ^ (-p)) t = c * t ^ (-p - k) := fun k => convWd_pow_formula k (-p)
  choose c hc using hf
  have hpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : ℝ => u ^ (-p)) (Ioi 0) :=
    fun u hu => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hu)).contDiffWithinAt
  refine ⟨fun k => |c k|, fun t ht => ?_, fun k t ht => ?_⟩
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t + 1) t := by fun_prop
    exact (h1.rpow_const_of_ne (ne_of_gt (by have : (0 : ℝ) < t := ht; linarith))).contDiffWithinAt
  · have hpos : (0 : ℝ) < t + 1 := by linarith
    have hm : (1 : ℝ) * t + 1 ∈ Ioi (0 : ℝ) := by
      show (0 : ℝ) < 1 * t + 1; linarith
    have e := convWd_affine (Ioi 0) isOpen_Ioi 1 1 k (fun u => u ^ (-p)) hpow t hm
    simp only [one_mul, one_pow] at e
    rw [e, hc k (t + 1) hpos]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    show |c k * (t + 1) ^ (-p - k)| ≤ |c k| * t ^ (-p - k)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht (by linarith) (by linarith))
      (abs_nonneg _)

/-- `ϱ(t) = (t/(1+t))^p` is good with exponent `0`, for `p ≥ 1/2`. -/
lemma convWd_rho (p : ℝ) (hp : 1 / 2 < p) : ∃ C : ℕ → ℝ, convWdGood 0 (convRho p) C := by
  obtain ⟨C1, h1⟩ := convWd_pow p
  obtain ⟨C2, h2⟩ := convWd_shift p (by linarith)
  have hm := convWd_mul h1 h2
  refine ⟨convWdMulSeq C1 C2, convWd_congr hm ?_ (by ring)⟩
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  show t ^ p * (t + 1) ^ (-p) = (t / (1 + t)) ^ p
  rw [Real.div_rpow ht'.le (by linarith), Real.rpow_neg (by linarith), add_comm 1 t, div_eq_mul_inv]

/-- The cutoff `η = convEta` is good with exponent `0`. -/
lemma convWd_eta : ∃ C : ℕ → ℝ, convWdGood 0 convEta C := by
  have hM : ∀ k : ℕ, ∃ M : ℝ, ∀ y ∈ Icc (0 : ℝ) 2, |iteratedDeriv k convEta y| ≤ M := by
    intro k
    have hc : ContinuousOn (iteratedDeriv k convEta) (Icc 0 2) :=
      (ContDiff.continuous_iteratedDeriv k (convEta_contDiff (n := ⊤)) (by exact_mod_cast le_top)).continuousOn
    obtain ⟨M, hM⟩ := (isCompact_Icc).exists_bound_of_continuousOn hc
    exact ⟨M, fun y hy => by simpa [Real.norm_eq_abs] using hM y hy⟩
  choose M hM using hM
  refine ⟨fun k => max (M k) 1 * 2 ^ k, convEta_contDiff.contDiffOn, fun k y hy => ?_⟩
  by_cases hy2 : y ≤ 2
  · have hb := hM k y ⟨hy.le, hy2⟩
    have hpow : (1 : ℝ) ≤ 2 ^ k * y ^ (-0 - (k : ℝ)) := by
      rw [show (-0 - (k : ℝ)) = -(k : ℝ) by ring, Real.rpow_neg hy.le, Real.rpow_natCast,
        ← div_eq_mul_inv, le_div_iff₀ (pow_pos hy k), one_mul]
      exact pow_le_pow_left₀ hy.le hy2 k
    have hmax : (0 : ℝ) ≤ max (M k) 1 := le_trans zero_le_one (le_max_right _ _)
    calc |iteratedDeriv k convEta y| ≤ M k := hb
      _ ≤ max (M k) 1 := le_max_left _ _
      _ = max (M k) 1 * 1 := (mul_one _).symm
      _ ≤ max (M k) 1 * (2 ^ k * y ^ (-0 - (k : ℝ))) := mul_le_mul_of_nonneg_left hpow hmax
      _ = max (M k) 1 * 2 ^ k * y ^ (-0 - (k : ℝ)) := by ring
  · have hy2' : y ∈ Ioi (2 : ℝ) := lt_of_not_ge hy2
    have hmax : (1 : ℝ) ≤ max (M k) 1 := le_max_right _ _
    cases k with
    | zero =>
      have h1 : |convEta y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [convEta_nonneg y], convEta_le_one y⟩
      simp only [Nat.cast_zero, neg_zero, zero_sub, Real.rpow_zero, mul_one, pow_zero]
      exact h1.trans hmax
    | succ m =>
      have heq : Set.EqOn convEta (fun _ => (1 : ℝ)) (Ioi 2) :=
        fun x hx => convEta_eq_one (le_of_lt hx)
      have e := (Set.EqOn.iteratedDeriv_of_isOpen heq isOpen_Ioi (m + 1)) hy2'
      rw [e, iteratedDeriv_const]
      simp only [Nat.add_one_ne_zero, ite_false, abs_zero]
      have hnn : (0 : ℝ) ≤ max (M (m + 1)) 1 * 2 ^ (m + 1) * y ^ (-0 - ((m + 1 : ℕ) : ℝ)) :=
        mul_nonneg (mul_nonneg (le_trans zero_le_one hmax) (by positivity))
          (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_two hy2')) _)
      exact hnn

/-- Scaling: `∂^k [ϱ(h y)] = h^k (∂^k ϱ)(h y)`, and the constants do not depend on `h`. -/
lemma convWd_scale {p h : ℝ} {C : ℕ → ℝ} (hρ : convWdGood 0 (convRho p) C) (hh : 0 < h) :
    convWdGood 0 (fun y => convRho p (h * y)) C := by
  refine ⟨?_, fun k y hy => ?_⟩
  · exact hρ.1.comp ((contDiff_const.mul contDiff_id).contDiffOn)
      (fun y hy => mul_pos hh hy)
  · have hm : h * y + 0 ∈ Ioi (0 : ℝ) := by
      rw [add_zero]; exact mul_pos hh hy
    have hd := convWd_affine (Ioi 0) isOpen_Ioi h 0 k (convRho p) hρ.1 y hm
    simp only [add_zero] at hd
    rw [hd, abs_mul, abs_of_nonneg (pow_nonneg hh.le k)]
    have hb := hρ.2 k (h * y) (mul_pos hh hy)
    have hid : h ^ k * h ^ (-0 - (k : ℝ)) = 1 := by
      rw [show (-0 - (k : ℝ)) = -(k : ℝ) by ring, Real.rpow_neg hh.le, Real.rpow_natCast]
      field_simp
    calc h ^ k * |iteratedDeriv k (convRho p) (h * y)|
        ≤ h ^ k * (C k * (h * y) ^ (-0 - (k : ℝ))) := mul_le_mul_of_nonneg_left hb (pow_nonneg hh.le k)
      _ = C k * (h ^ k * h ^ (-0 - (k : ℝ))) * y ^ (-0 - (k : ℝ)) := by
          rw [Real.mul_rpow hh.le hy.le]; ring
      _ = C k * y ^ (-0 - (k : ℝ)) := by rw [hid, mul_one]

/-- The full weight: `w_h` is good with exponent `3/2`, with constants independent of `h`. -/
lemma convWd_weight {p h : ℝ} (hh : 0 < h) {Cη Cρ Cp : ℕ → ℝ}
    (hη : convWdGood 0 convEta Cη) (hρ : convWdGood 0 (convRho p) Cρ)
    (hpw : convWdGood (-(-(3 / 2 : ℝ))) (fun t => t ^ (-(3 / 2 : ℝ))) Cp) :
    convWdGood (3 / 2) (convWh p h) (convWdMulSeq (convWdMulSeq Cη Cρ) Cp) := by
  have hG1 := convWd_mul hη (convWd_scale (p := p) (h := h) hρ hh)
  have hG2 := convWd_mul hG1 hpw
  refine convWd_congr hG2 ?_ (by norm_num)
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  show convEta t * convRho p (h * t) * t ^ (-(3 / 2 : ℝ)) = convWh p h t
  unfold convWh
  rw [Real.rpow_neg ht'.le]
  ring

/-- `(ceo:conv.4)`: `|∂^r w_h(y)| ≤ C_r y^{-3/2-r}` for `y ≥ 1`, with `C_r` depending on `p, r` only
(the existential precedes `h`, so it is uniform in `h > 0`). `iteratedDeriv` is the genuine derivative
here: `w_h` coincides near every `y > 0` with a smooth product, and `y ≥ 1`. The hypothesis `p < 1`
is not used (the bound holds for every `p ≥ 1/2` here) and is kept to match the TeX range. -/
theorem convW_deriv_bound {p : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (r : ℕ) :
    ∃ C : ℝ, ∀ h : ℝ, 0 < h → ∀ y : ℝ, 1 ≤ y →
      |iteratedDeriv r (convWh p h) y| ≤ C * y ^ (-(3 / 2 : ℝ) - r) := by
  obtain ⟨Cρ, hρ⟩ := convWd_rho p hp
  obtain ⟨Cη, hη⟩ := convWd_eta
  obtain ⟨Cp, hpw⟩ := convWd_pow (-(3 / 2 : ℝ))
  refine ⟨convWdMulSeq (convWdMulSeq Cη Cρ) Cp r, fun h hh y hy => ?_⟩
  have hG := convWd_weight hh hη hρ hpw
  exact hG.2 r y (by linarith)

/-- info: 'FormalResearch.SignUncertainty.convWd_cdk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_cdk

/-- info: 'FormalResearch.SignUncertainty.convWd_pow_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_pow_formula

/-- info: 'FormalResearch.SignUncertainty.convWd_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_affine

/-- info: 'FormalResearch.SignUncertainty.convWd_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_contDiffAt

/-- info: 'FormalResearch.SignUncertainty.convWd_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_mul

/-- info: 'FormalResearch.SignUncertainty.convWd_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_congr

/-- info: 'FormalResearch.SignUncertainty.convWd_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_pow

/-- info: 'FormalResearch.SignUncertainty.convWd_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_shift

/-- info: 'FormalResearch.SignUncertainty.convWd_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_rho

/-- info: 'FormalResearch.SignUncertainty.convWd_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_eta

/-- info: 'FormalResearch.SignUncertainty.convWd_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_scale

/-- info: 'FormalResearch.SignUncertainty.convWd_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convWd_weight

/-- info: 'FormalResearch.SignUncertainty.convW_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convW_deriv_bound

end FormalResearch.SignUncertainty
