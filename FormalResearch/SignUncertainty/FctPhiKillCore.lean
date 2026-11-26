module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# `fct:phikill` (1)–(2): properties and exact Cauchy moments of `φ_{p,q}` and `φ_kill` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.4 (`fct:phikill`),
parts (1) and (2) (lines 298–354).

For integers `p, q ≥ 1` and `a > 0`:
* `phiPQ p q a z = ∑_{l=p}^{p+q-1} C(p+q-1, l) (z/(z+a))^l (a/(z+a))^{p+q-1-l}`,
* `phiKill a z = phiPQ 8 8 a z`.

Main results proved here:
* `one_sub_phiPQ`: complement binomial sum `1 - φ_{p,q}(z; a) = ∑_{l=0}^{p-1} ...`.
* `differentiableOn_phiPQ`, `phiPQ_conj`, `phiPQ_pos_real`, `phiPQ_lt_one_real`.
* `hasDerivAt_phiPQ`: exact telescoping derivative `∂_z φ_{p,q}(z; a) = p C(p+q-1, p) a^q z^{p-1} / (z+a)^{p+q}`.
* `norm_phiPQ_le`, `norm_one_sub_phiPQ_le`, `norm_iteratedDeriv_phiPQ_le`,
  `phiKill_near_zero`, `one_sub_phiKill_near_inf`, `abs_im_phiKill_le`.
* `phiPQ_moment_neg` and `phiPQ_moment_pos`: exact Cauchy moment vanishing `(fct:pk-cauchy)`
  for all `p, q ≥ 1`, proved via partial-fraction expansion in `(z + a)^{-d}` (`d ≥ 2`) and
  the fundamental theorem of calculus (no contour integration required).

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctPhiKill

/-- General order-`(p, q)` holomorphic binomial cutoff `φ_{p,q}(z; a)`. -/
noncomputable def phiPQ (p q : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  ∑ l ∈ Finset.Ico p (p + q),
    ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * (z / (z + a)) ^ l * ((a : ℂ) / (z + a)) ^ (p + q - 1 - l)

/-- Order-8 holomorphic binomial cutoff `φ_kill(z; a) = φ_{8,8}(z; a)` of `(fct:phikill-def)`. -/
noncomputable def phiKill (a : ℝ) (z : ℂ) : ℂ := phiPQ 8 8 a z

/-! ### Algebraic identities, symmetry, holomorphicity, and real-axis positivity -/

lemma add_ofReal_ne_zero_of_re_nonneg {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.re) :
    z + (a : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
  linarith

lemma norm_add_ofReal_ge {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 ≤ z.re) :
    max ‖z‖ a ≤ ‖z + (a : ℂ)‖ := by
  have hsq : ‖z + (a : ℂ)‖ ^ 2 = ‖z‖ ^ 2 + 2 * a * z.re + a ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    ring
  have hre : 0 ≤ 2 * a * z.re := by positivity
  rw [max_le_iff]
  constructor
  · exact le_of_sq_le_sq (by nlinarith [sq_nonneg a]) (norm_nonneg _)
  · exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖z‖]) (norm_nonneg _)

/-- Complement binomial sum `1 - φ_{p,q}(z; a) = ∑_{l=0}^{p-1} C(p+q-1, l) (z/(z+a))^l (a/(z+a))^{p+q-1-l}`. -/
lemma one_sub_phiPQ {p q : ℕ} (hq : 1 ≤ q) {a : ℝ} {z : ℂ} (hza : z + (a : ℂ) ≠ 0) :
    1 - phiPQ p q a z =
      ∑ l ∈ Finset.range p,
        ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * (z / (z + a)) ^ l * ((a : ℂ) / (z + a)) ^ (p + q - 1 - l) := by
  have hsum1 : z / (z + a) + (a : ℂ) / (z + a) = 1 := by
    rw [← add_div, div_self hza]
  have hbin : (1 : ℂ) =
      ∑ l ∈ Finset.range (p + q),
        ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * (z / (z + a)) ^ l * ((a : ℂ) / (z + a)) ^ (p + q - 1 - l) := by
    have h1 := add_pow (z / (z + a)) ((a : ℂ) / (z + a)) (p + q - 1)
    rw [hsum1, one_pow, show p + q - 1 + 1 = p + q by omega] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast; ring
  have hsplit : Finset.range (p + q) = Finset.range p ∪ Finset.Ico p (p + q) := by
    ext l; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range p) (Finset.Ico p (p + q)) := by
    rw [Finset.disjoint_left]; intro l h1 h2
    simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj] at hbin
  unfold phiPQ
  linear_combination hbin

lemma phiPQ_scale {p q : ℕ} {a : ℝ} (ha : 0 < a) (z : ℂ) :
    phiPQ p q a z = phiPQ p q 1 (z / (a : ℂ)) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold phiPQ
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : z / (z + (a : ℂ)) = (z / (a : ℂ)) / (z / (a : ℂ) + (1 : ℝ)) := by
    simp only [Complex.ofReal_one]
    field_simp
  have h2 : (a : ℂ) / (z + (a : ℂ)) = ((1 : ℝ) : ℂ) / (z / (a : ℂ) + (1 : ℝ)) := by
    simp only [Complex.ofReal_one]
    field_simp
  rw [h1, h2]

lemma differentiableOn_phiPQ (p q : ℕ) (a : ℝ) :
    DifferentiableOn ℂ (phiPQ p q a) {z : ℂ | z ≠ -(a : ℂ)} := by
  unfold phiPQ
  intro z hz
  have hza : z + (a : ℂ) ≠ 0 := by
    intro h; apply hz; linear_combination h
  have hd : DifferentiableAt ℂ (fun w : ℂ =>
      ∑ l ∈ Finset.Ico p (p + q),
        ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * (w / (w + a)) ^ l * ((a : ℂ) / (w + a)) ^ (p + q - 1 - l)) z := by
    refine DifferentiableAt.fun_sum fun l _ => ?_
    have h1 : DifferentiableAt ℂ (fun w : ℂ => w / (w + (a : ℂ))) z :=
      differentiableAt_id.div (differentiableAt_id.add (differentiableAt_const _)) hza
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (a : ℂ) / (w + (a : ℂ))) z :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) hza
    exact ((differentiableAt_const _).mul (h1.pow l)).mul (h2.pow _)
  exact hd.differentiableWithinAt

lemma phiPQ_conj (p q : ℕ) (a : ℝ) (z : ℂ) :
    phiPQ p q a (starRingEnd ℂ z) = starRingEnd ℂ (phiPQ p q a z) := by
  unfold phiPQ
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [map_mul, map_pow, map_div₀, map_add, Complex.conj_ofReal]

lemma phiPQ_imag_even_re (p q : ℕ) (a t : ℝ) :
    (phiPQ p q a ((-t : ℝ) * Complex.I)).re = (phiPQ p q a ((t : ℝ) * Complex.I)).re := by
  have h : ((-t : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((t : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal]
  rw [h, phiPQ_conj, Complex.conj_re]

lemma phiPQ_imag_odd_im (p q : ℕ) (a t : ℝ) :
    (phiPQ p q a ((-t : ℝ) * Complex.I)).im = -(phiPQ p q a ((t : ℝ) * Complex.I)).im := by
  have h : ((-t : ℝ) : ℂ) * Complex.I = starRingEnd ℂ ((t : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal]
  rw [h, phiPQ_conj, Complex.conj_im]

lemma phiPQ_ofReal (p q : ℕ) (a σ : ℝ) :
    phiPQ p q a (σ : ℂ) =
      ((∑ l ∈ Finset.Ico p (p + q),
        (Nat.choose (p + q - 1) l : ℝ) * (σ / (σ + a)) ^ l * (a / (σ + a)) ^ (p + q - 1 - l) : ℝ) : ℂ) := by
  unfold phiPQ
  push_cast
  rfl

lemma phiPQ_pos_and_lt_one_real {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    0 < (phiPQ p q a (σ : ℂ)).re ∧ (phiPQ p q a (σ : ℂ)).re < 1 ∧ (phiPQ p q a (σ : ℂ)).im = 0 := by
  have hza : (σ : ℂ) + (a : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  rw [phiPQ_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, ?_, rfl⟩
  · have hmem : p ∈ Finset.Ico p (p + q) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hpos_p : 0 < (Nat.choose (p + q - 1) p : ℝ) * (σ / (σ + a)) ^ p * (a / (σ + a)) ^ (p + q - 1 - p) := by
      have hc : 0 < Nat.choose (p + q - 1) p := Nat.choose_pos (by omega)
      have hc' : (0 : ℝ) < (Nat.choose (p + q - 1) p : ℝ) := Nat.cast_pos.mpr hc
      positivity
    have hnn : ∀ l ∈ Finset.Ico p (p + q),
        0 ≤ (Nat.choose (p + q - 1) l : ℝ) * (σ / (σ + a)) ^ l * (a / (σ + a)) ^ (p + q - 1 - l) :=
      fun l _ => by positivity
    exact lt_of_lt_of_le hpos_p (Finset.single_le_sum hnn hmem)
  · have hcomp := one_sub_phiPQ (p := p) hq hza
    have hre := congrArg Complex.re hcomp
    rw [Complex.sub_re, Complex.one_re, phiPQ_ofReal, Complex.ofReal_re] at hre
    have hrhs : (∑ l ∈ Finset.range p,
        ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * ((σ : ℂ) / ((σ : ℂ) + a)) ^ l *
          ((a : ℂ) / ((σ : ℂ) + a)) ^ (p + q - 1 - l)).re =
        ∑ l ∈ Finset.range p,
          (Nat.choose (p + q - 1) l : ℝ) * (σ / (σ + a)) ^ l * (a / (σ + a)) ^ (p + q - 1 - l) := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : ((Nat.choose (p + q - 1) l : ℝ) : ℂ) * ((σ : ℂ) / ((σ : ℂ) + a)) ^ l *
          ((a : ℂ) / ((σ : ℂ) + a)) ^ (p + q - 1 - l) =
          (((Nat.choose (p + q - 1) l : ℝ) * (σ / (σ + a)) ^ l * (a / (σ + a)) ^ (p + q - 1 - l) : ℝ) : ℂ) := by
        push_cast; rfl
      rw [this, Complex.ofReal_re]
    rw [hrhs] at hre
    have h0mem : 0 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
    have hpos0 : 0 < (Nat.choose (p + q - 1) 0 : ℝ) * (σ / (σ + a)) ^ 0 * (a / (σ + a)) ^ (p + q - 1 - 0) := by
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul, Nat.sub_zero]
      positivity
    have hnn : ∀ l ∈ Finset.range p,
        0 ≤ (Nat.choose (p + q - 1) l : ℝ) * (σ / (σ + a)) ^ l * (a / (σ + a)) ^ (p + q - 1 - l) :=
      fun l _ => by positivity
    have hpos_sub := lt_of_lt_of_le hpos0 (Finset.single_le_sum hnn h0mem)
    linarith

/-! ### Exact telescoping derivative of `φ_{p,q}` -/

lemma hasDerivAt_phiPQ {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {a : ℝ} {z : ℂ} (hza : z + (a : ℂ) ≠ 0) :
    HasDerivAt (phiPQ p q a)
      ((p : ℂ) * ((Nat.choose (p + q - 1) p : ℝ) : ℂ) * (a : ℂ) ^ q * z ^ (p - 1) / (z + a) ^ (p + q)) z := by
  set n : ℕ := p + q - 1
  have hn_eq : n + 1 = p + q := by omega
  have hx : HasDerivAt (fun w : ℂ => w / (w + (a : ℂ))) ((a : ℂ) / (z + a) ^ 2) z := by
    have h1 := (hasDerivAt_id z).div ((hasDerivAt_id z).add_const (a : ℂ)) hza
    refine h1.congr_deriv ?_; simp only [id_eq]; ring
  have hy : HasDerivAt (fun w : ℂ => (a : ℂ) / (w + (a : ℂ))) (-((a : ℂ) / (z + a) ^ 2)) z := by
    have h1 := (hasDerivAt_const z (a : ℂ)).div ((hasDerivAt_id z).add_const (a : ℂ)) hza
    refine h1.congr_deriv ?_; simp only [id_eq]; ring
  set x : ℂ := z / (z + a)
  set y : ℂ := (a : ℂ) / (z + a)
  -- Differentiate the sum term by term
  have hsum_deriv : HasDerivAt (phiPQ p q a)
      (∑ l ∈ Finset.Ico p (n + 1),
        ((Nat.choose n l : ℝ) : ℂ) *
          (((l : ℂ) * x ^ (l - 1) * ((a : ℂ) / (z + a) ^ 2)) * y ^ (n - l) +
            x ^ l * (((n - l : ℕ) : ℂ) * y ^ (n - l - 1) * (-((a : ℂ) / (z + a) ^ 2))))) z := by
    unfold phiPQ
    rw [show p + q = n + 1 by omega]
    refine HasDerivAt.fun_sum fun l _ => ?_
    have hd1 := (hx.pow l).const_mul ((Nat.choose n l : ℝ) : ℂ)
    have hd2 := hy.pow (n - l)
    have hm := hd1.mul hd2
    refine hm.congr_deriv ?_
    simp only [Pi.pow_apply, x, y]; ring
  refine hsum_deriv.congr_deriv ?_
  -- Factor out `a / (z + a)^2` and telescope the binomial sum
  set dx : ℂ := (a : ℂ) / (z + a) ^ 2
  have htele : ∑ l ∈ Finset.Ico p (n + 1),
      ((Nat.choose n l : ℝ) : ℂ) *
        (((l : ℂ) * x ^ (l - 1) * dx) * y ^ (n - l) +
          x ^ l * (((n - l : ℕ) : ℂ) * y ^ (n - l - 1) * (-dx))) =
      dx * ((p : ℂ) * ((Nat.choose n p : ℝ) : ℂ) * x ^ (p - 1) * y ^ (n - p)) := by
    let F : ℕ → ℂ := fun l =>
      if l ≤ n then (l : ℂ) * ((Nat.choose n l : ℝ) : ℂ) * x ^ (l - 1) * y ^ (n - l) else 0
    have hterm : ∀ l ∈ Finset.Ico p (n + 1),
        ((Nat.choose n l : ℝ) : ℂ) *
          (((l : ℂ) * x ^ (l - 1) * dx) * y ^ (n - l) +
            x ^ l * (((n - l : ℕ) : ℂ) * y ^ (n - l - 1) * (-dx))) =
          dx * (F l - F (l + 1)) := by
      intro l hl
      have hl_le : l ≤ n := by have := (Finset.mem_Ico.mp hl).2; omega
      simp only [F, hl_le, ↓reduceIte]
      by_cases hln : l = n
      · subst hln
        have hnot : ¬ (n + 1 ≤ n) := by omega
        simp only [hnot, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero, sub_zero]
        ring
      · have hl1 : l + 1 ≤ n := by omega
        simp only [hl1, ↓reduceIte, Nat.add_sub_cancel]
        have hbin_id : (n - l) * Nat.choose n l = (l + 1) * Nat.choose n (l + 1) := by
          have h2 := Nat.choose_succ_right_eq n l
          linarith
        have hbinC : ((n - l : ℕ) : ℂ) * ((Nat.choose n l : ℝ) : ℂ) =
            ((l + 1 : ℕ) : ℂ) * ((Nat.choose n (l + 1) : ℝ) : ℂ) := by
          exact_mod_cast hbin_id
        have hsub : n - l - 1 = n - (l + 1) := by omega
        rw [hsub]
        have : ((Nat.choose n l : ℝ) : ℂ) * (x ^ l * (((n - l : ℕ) : ℂ) * y ^ (n - (l + 1)) * (-dx))) =
            -(dx * (((l + 1 : ℕ) : ℂ) * ((Nat.choose n (l + 1) : ℝ) : ℂ) * x ^ l * y ^ (n - (l + 1)))) := by
          calc ((Nat.choose n l : ℝ) : ℂ) * (x ^ l * (((n - l : ℕ) : ℂ) * y ^ (n - (l + 1)) * (-dx)))
              = -(dx * ((((n - l : ℕ) : ℂ) * ((Nat.choose n l : ℝ) : ℂ)) * x ^ l * y ^ (n - (l + 1)))) := by ring
            _ = -(dx * (((l + 1 : ℕ) : ℂ) * ((Nat.choose n (l + 1) : ℝ) : ℂ) * x ^ l * y ^ (n - (l + 1)))) := by
                rw [hbinC]
        push_cast at this ⊢
        linear_combination this
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hsum_tele : ∀ (m : ℕ), p ≤ m → ∑ l ∈ Finset.Ico p m, (F l - F (l + 1)) = F p - F m := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hpm : p ≤ m
        · rw [Finset.sum_Ico_succ_top hpm, ih hpm]; ring
        · have : p = m + 1 := by omega
          rw [this]; simp
    rw [hsum_tele (n + 1) (by omega)]
    have hp_le : p ≤ n := by omega
    have hn1 : ¬ (n + 1 ≤ n) := by omega
    simp only [F, hp_le, hn1, ↓reduceIte, sub_zero]
  rw [htele]
  simp only [dx, x, y]
  have hnp : n - p = q - 1 := by omega
  rw [hnp, div_pow, div_pow]
  have hza_pow : (z + (a : ℂ)) ^ 2 * (z + (a : ℂ)) ^ (p - 1) * (z + (a : ℂ)) ^ (q - 1) = (z + (a : ℂ)) ^ (p + q) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have ha_pow : (a : ℂ) * (a : ℂ) ^ (q - 1) = (a : ℂ) ^ q := by
    rw [← pow_succ']; congr 1; omega
  calc (a : ℂ) / (z + a) ^ 2 * ((p : ℂ) * ((Nat.choose n p : ℝ) : ℂ) * (z ^ (p - 1) / (z + a) ^ (p - 1)) *
          ((a : ℂ) ^ (q - 1) / (z + a) ^ (q - 1)))
      = (p : ℂ) * ((Nat.choose n p : ℝ) : ℂ) * ((a : ℂ) * (a : ℂ) ^ (q - 1)) * z ^ (p - 1) /
          ((z + a) ^ 2 * (z + a) ^ (p - 1) * (z + a) ^ (q - 1)) := by
          field_simp [hza]
    _ = (p : ℂ) * ((Nat.choose n p : ℝ) : ℂ) * (a : ℂ) ^ q * z ^ (p - 1) / (z + a) ^ (p + q) := by
        rw [ha_pow, hza_pow]

/-! ### Uniform bounds and asymptotic expansions on `Re z ≥ 0` -/

lemma norm_phiPQ_le (p q : ℕ) :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖phiPQ p q a z‖ ≤ C * min ((‖z‖ / a) ^ p) 1 := by
  set C : ℝ := ∑ l ∈ Finset.Ico p (p + q), (Nat.choose (p + q - 1) l : ℝ)
  refine ⟨C, Finset.sum_nonneg fun l _ => Nat.cast_nonneg _, fun {a z} ha hz => ?_⟩
  have hza_ge := norm_add_ofReal_ge ha hz
  have hz_le : ‖z‖ / ‖z + (a : ℂ)‖ ≤ 1 :=
    (div_le_one (lt_of_lt_of_le ha (le_trans (le_max_right _ _) hza_ge))).mpr
      (le_trans (le_max_left _ _) hza_ge)
  have ha_le : a / ‖z + (a : ℂ)‖ ≤ 1 :=
    (div_le_one (lt_of_lt_of_le ha (le_trans (le_max_right _ _) hza_ge))).mpr
      (le_trans (le_max_right _ _) hza_ge)
  have hz_div_a : ‖z‖ / ‖z + (a : ℂ)‖ ≤ ‖z‖ / a :=
    div_le_div_of_nonneg_left (norm_nonneg z) ha (le_trans (le_max_right _ _) hza_ge)
  unfold phiPQ
  refine (norm_sum_le _ _).trans ?_
  rw [show C * min ((‖z‖ / a) ^ p) 1 =
      ∑ l ∈ Finset.Ico p (p + q), (Nat.choose (p + q - 1) l : ℝ) * min ((‖z‖ / a) ^ p) 1 by
    simp only [C, Finset.sum_mul]]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlp : p ≤ l := (Finset.mem_Ico.mp hl).1
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos ha]
  have hpow_a : (a / ‖z + (a : ℂ)‖) ^ (p + q - 1 - l) ≤ 1 := pow_le_one₀ (by positivity) ha_le
  have hpow_z : (‖z‖ / ‖z + (a : ℂ)‖) ^ l ≤ min ((‖z‖ / a) ^ p) 1 := by
    rw [le_min_iff]
    refine ⟨?_, pow_le_one₀ (by positivity) hz_le⟩
    calc (‖z‖ / ‖z + (a : ℂ)‖) ^ l
        ≤ (‖z‖ / ‖z + (a : ℂ)‖) ^ p := pow_le_pow_of_le_one (by positivity) hz_le hlp
      _ ≤ (‖z‖ / a) ^ p := pow_le_pow_left₀ (by positivity) hz_div_a p
  calc (Nat.choose (p + q - 1) l : ℝ) * (‖z‖ / ‖z + (a : ℂ)‖) ^ l * (a / ‖z + (a : ℂ)‖) ^ (p + q - 1 - l)
      ≤ (Nat.choose (p + q - 1) l : ℝ) * (‖z‖ / ‖z + (a : ℂ)‖) ^ l * 1 :=
        mul_le_mul_of_nonneg_left hpow_a (by positivity)
    _ ≤ (Nat.choose (p + q - 1) l : ℝ) * min ((‖z‖ / a) ^ p) 1 := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hpow_z (Nat.cast_nonneg _)

lemma norm_one_sub_phiPQ_le (p q : ℕ) (hq : 1 ≤ q) :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖1 - phiPQ p q a z‖ ≤ C * min 1 ((a / ‖z‖) ^ q) ∨ z = 0 := by
  -- Even cleaner: state both `‖1 - φ‖ ≤ C` and for `z ≠ 0`, `‖1 - φ‖ ≤ C * (a / ‖z‖)^q`
  set C : ℝ := ∑ l ∈ Finset.range p, (Nat.choose (p + q - 1) l : ℝ)
  refine ⟨C, Finset.sum_nonneg fun l _ => Nat.cast_nonneg _, fun {a z} ha hz => ?_⟩
  by_cases hz0 : z = 0
  · exact Or.inr hz0
  left
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hza_ne := add_ofReal_ne_zero_of_re_nonneg ha hz
  have hza_ge := norm_add_ofReal_ge ha hz
  have hz_le : ‖z‖ / ‖z + (a : ℂ)‖ ≤ 1 :=
    (div_le_one (lt_of_lt_of_le ha (le_trans (le_max_right _ _) hza_ge))).mpr
      (le_trans (le_max_left _ _) hza_ge)
  have ha_le : a / ‖z + (a : ℂ)‖ ≤ 1 :=
    (div_le_one (lt_of_lt_of_le ha (le_trans (le_max_right _ _) hza_ge))).mpr
      (le_trans (le_max_right _ _) hza_ge)
  have ha_div_z : a / ‖z + (a : ℂ)‖ ≤ a / ‖z‖ :=
    div_le_div_of_nonneg_left ha.le hz_pos (le_trans (le_max_left _ _) hza_ge)
  rw [one_sub_phiPQ hq hza_ne]
  refine (norm_sum_le _ _).trans ?_
  rw [show C * min 1 ((a / ‖z‖) ^ q) =
      ∑ l ∈ Finset.range p, (Nat.choose (p + q - 1) l : ℝ) * min 1 ((a / ‖z‖) ^ q) by
    simp only [C, Finset.sum_mul]]
  refine Finset.sum_le_sum fun l hl => ?_
  have hlp : l < p := Finset.mem_range.mp hl
  have hq_le : q ≤ p + q - 1 - l := by omega
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos ha]
  have hpow_z : (‖z‖ / ‖z + (a : ℂ)‖) ^ l ≤ 1 := pow_le_one₀ (by positivity) hz_le
  have hpow_a : (a / ‖z + (a : ℂ)‖) ^ (p + q - 1 - l) ≤ min 1 ((a / ‖z‖) ^ q) := by
    rw [le_min_iff]
    refine ⟨pow_le_one₀ (by positivity) ha_le, ?_⟩
    calc (a / ‖z + (a : ℂ)‖) ^ (p + q - 1 - l)
        ≤ (a / ‖z + (a : ℂ)‖) ^ q := pow_le_pow_of_le_one (by positivity) ha_le hq_le
      _ ≤ (a / ‖z‖) ^ q := pow_le_pow_left₀ (by positivity) ha_div_z q
  calc (Nat.choose (p + q - 1) l : ℝ) * (‖z‖ / ‖z + (a : ℂ)‖) ^ l * (a / ‖z + (a : ℂ)‖) ^ (p + q - 1 - l)
      ≤ (Nat.choose (p + q - 1) l : ℝ) * 1 * min 1 ((a / ‖z‖) ^ q) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow_z (Nat.cast_nonneg _)) hpow_a
          (by positivity) (by positivity)
    _ = (Nat.choose (p + q - 1) l : ℝ) * min 1 ((a / ‖z‖) ^ q) := by ring

lemma norm_one_sub_phiPQ_le_one_and_tail (p q : ℕ) (hq : 1 ≤ q) :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖1 - phiPQ p q a z‖ ≤ C ∧ (z ≠ 0 → ‖1 - phiPQ p q a z‖ ≤ C * (a / ‖z‖) ^ q) := by
  obtain ⟨C, hC, hbd⟩ := norm_one_sub_phiPQ_le p q hq
  refine ⟨max C 1, by positivity, fun {a z} ha hz => ?_⟩
  rcases hbd ha hz with h | rfl
  · refine ⟨(h.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)).trans (by linarith [le_max_left C 1]),
      fun _ => (h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)).trans
        (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))⟩
  · refine ⟨?_, fun h => absurd rfl h⟩
    by_cases hp : p = 0
    · subst hp
      have hza : (0 : ℂ) + (a : ℂ) ≠ 0 := by simp [ha.ne']
      rw [one_sub_phiPQ hq hza]
      simp
    · have h0 : phiPQ p q a 0 = 0 := by
        unfold phiPQ
        refine Finset.sum_eq_zero fun l hl => ?_
        have hlp : l ≠ 0 := by have := (Finset.mem_Ico.mp hl).1; omega
        simp [zero_div, zero_pow hlp]
      rw [h0, sub_zero, norm_one]; exact le_max_right C 1

/-- Higher derivative bounds on `Re z ≥ 0`, `z ≠ 0`:
`‖∂_z^r φ_{p,q}(z; a)‖ ≤ C_{p,q,r} min(|z|^{p-r} a^{-p}, a^q |z|^{-q-r})` for `r ≥ 1`. -/
lemma norm_iteratedDeriv_phiPQ_le (p q r : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re → z ≠ 0 →
      ‖iteratedDeriv r (phiPQ p q a) z‖ ≤
        C * min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ))) := by
  -- Helper: iterated derivatives of `w ↦ w^m` and `w ↦ (w + a)^{-M}`
  have hpow_deriv : ∀ (k m : ℕ) (w : ℂ),
      ‖iteratedDeriv k (fun u : ℂ => u ^ m) w‖ ≤ (m.factorial : ℝ) * ‖w‖ ^ ((m : ℤ) - k) ∨ w = 0 := by
    intro k
    induction k with
    | zero =>
      intro m w
      left; simp only [iteratedDeriv_zero, norm_pow, Nat.cast_zero, sub_zero, zpow_natCast]
      exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg w) m) (by exact_mod_cast Nat.factorial_pos m)
    | succ k ih =>
      intro m w
      by_cases hw : w = 0
      · exact Or.inr hw
      left
      rw [iteratedDeriv_succ']
      have hderiv_pow : deriv (fun u : ℂ => u ^ m) = fun u => (m : ℂ) * u ^ (m - 1) := by
        ext u; exact (hasDerivAt_pow m u).deriv
      rw [hderiv_pow, iteratedDeriv_const_mul_field]
      cases m with
      | zero => simp; exact zpow_nonneg (norm_nonneg w) _
      | succ m =>
        simp only [Nat.add_sub_cancel]
        rw [norm_mul, Complex.norm_natCast]
        rcases ih m w with h | h
        · have hfac : ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) = ((m + 1).factorial : ℝ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have hexp : ((m : ℤ) - k) = ((m + 1 : ℕ) : ℤ) - (k + 1 : ℕ) := by omega
          calc ((m + 1 : ℕ) : ℝ) * ‖iteratedDeriv k (fun u : ℂ => u ^ m) w‖
              ≤ ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℝ) * ‖w‖ ^ ((m : ℤ) - k)) :=
                mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
            _ = ((m + 1).factorial : ℝ) * ‖w‖ ^ (((m + 1 : ℕ) : ℤ) - (k + 1 : ℕ)) := by
                rw [← mul_assoc, hfac, hexp]
        · exact absurd h hw
  have hinv_deriv : ∀ (k M : ℕ) (a : ℝ) (w : ℂ), w + (a : ℂ) ≠ 0 →
      iteratedDeriv k (fun u : ℂ => (u + (a : ℂ)) ^ (-(M : ℤ))) w =
        (-1 : ℂ) ^ k * ((Nat.ascFactorial M k : ℝ) : ℂ) * (w + (a : ℂ)) ^ (-((M + k : ℕ) : ℤ)) := by
    intro k
    induction k with
    | zero => intro M a w _; simp
    | succ k ih =>
      intro M a w hwa
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {u : ℂ | u + (a : ℂ) ≠ 0} :=
        isOpen_ne.preimage (continuous_id.add continuous_const)
      have hev : iteratedDeriv k (fun u : ℂ => (u + (a : ℂ)) ^ (-(M : ℤ))) =ᶠ[𝓝 w]
          fun u => (-1 : ℂ) ^ k * ((Nat.ascFactorial M k : ℝ) : ℂ) * (u + (a : ℂ)) ^ (-((M + k : ℕ) : ℤ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hwa) fun u hu => ih M a u hu
      rw [hev.deriv_eq]
      have hd1 : HasDerivAt (fun u : ℂ => (u + (a : ℂ)) ^ (-((M + k : ℕ) : ℤ)))
          ((-((M + k : ℕ) : ℤ) : ℂ) * (w + (a : ℂ)) ^ (-((M + k : ℕ) : ℤ) - 1)) w := by
        simpa [Function.comp_def] using
          (hasDerivAt_zpow (-((M + k : ℕ) : ℤ)) (w + (a : ℂ)) (Or.inl hwa)).comp w
            ((hasDerivAt_id w).add_const (a : ℂ))
      rw [(hd1.const_mul ((-1 : ℂ) ^ k * ((Nat.ascFactorial M k : ℝ) : ℂ))).deriv]
      have hexp : (-((M + k : ℕ) : ℤ) - 1) = -((M + (k + 1) : ℕ) : ℤ) := by omega
      rw [hexp, Nat.ascFactorial_succ, pow_succ]
      push_cast; ring
  -- Now apply Leibniz rule to `deriv (phiPQ p q a)` at order `r - 1`
  set pref : ℝ := (p : ℝ) * (Nat.choose (p + q - 1) p : ℝ)
  set C : ℝ := pref * ∑ k ∈ Finset.range r,
    (Nat.choose (r - 1) k : ℝ) * ((p - 1).factorial : ℝ) * (Nat.ascFactorial (p + q) (r - 1 - k) : ℝ)
  refine ⟨C, mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => by positivity),
    fun {a z} ha hz hz0 => ?_⟩
  have hza_ne := add_ofReal_ne_zero_of_re_nonneg ha hz
  have hza_ge := norm_add_ofReal_ge ha hz
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hza_pos : 0 < ‖z + (a : ℂ)‖ := lt_of_lt_of_le ha (le_trans (le_max_right _ _) hza_ge)
  -- Express `iteratedDeriv r (phiPQ p q a) z = iteratedDeriv (r - 1) (deriv (phiPQ p q a)) z`
  have hiter_eq : iteratedDeriv r (phiPQ p q a) z =
      ((pref : ℂ) * (a : ℂ) ^ q) *
        iteratedDeriv (r - 1) (fun u : ℂ => u ^ (p - 1) * (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) z := by
    have hr1 : r = (r - 1) + 1 := by omega
    conv_lhs => rw [hr1]
    rw [iteratedDeriv_succ']
    have hopen : IsOpen {u : ℂ | u + (a : ℂ) ≠ 0} :=
      isOpen_ne.preimage (continuous_id.add continuous_const)
    have hev : deriv (phiPQ p q a) =ᶠ[𝓝 z]
        fun u : ℂ => ((pref : ℂ) * (a : ℂ) ^ q) * (u ^ (p - 1) * (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) :=
      Filter.eventually_of_mem (hopen.mem_nhds hza_ne) fun u hu => by
        dsimp only
        rw [(hasDerivAt_phiPQ hp hq hu).deriv, zpow_neg, zpow_natCast]
        simp only [pref]; push_cast; ring
    rw [(hev.iteratedDeriv (r - 1)).eq_of_nhds, iteratedDeriv_const_mul_field]
  rw [hiter_eq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ pref), norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hcd1 : ContDiffAt ℂ ((r - 1 : ℕ) : WithTop ℕ∞) (fun u : ℂ => u ^ (p - 1)) z :=
    (contDiffAt_id.pow (p - 1)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hcd2 : ContDiffAt ℂ ((r - 1 : ℕ) : WithTop ℕ∞) (fun u : ℂ => (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) z := by
    have hinv_eq : (fun u : ℂ => (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) =
        fun u => ((u + (a : ℂ)) ^ (p + q))⁻¹ := by ext u; rw [zpow_neg, zpow_natCast]
    rw [hinv_eq]
    exact (((contDiffAt_id.add contDiffAt_const).pow (p + q)).inv (pow_ne_zero _ hza_ne)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [show (fun u : ℂ => u ^ (p - 1) * (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) =
      (fun u : ℂ => u ^ (p - 1)) * (fun u : ℂ => (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) from rfl,
    iteratedDeriv_mul hcd1 hcd2, show r - 1 + 1 = r by omega]
  have hsum_le := norm_sum_le (Finset.range r)
    (fun k => (Nat.choose (r - 1) k : ℂ) * iteratedDeriv k (fun u : ℂ => u ^ (p - 1)) z *
      iteratedDeriv (r - 1 - k) (fun u : ℂ => (u + (a : ℂ)) ^ (-((p + q : ℕ) : ℤ))) z)
  refine (mul_le_mul_of_nonneg_left hsum_le (mul_nonneg (by positivity : 0 ≤ pref) (pow_nonneg ha.le q))).trans ?_
  rw [show C * min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ))) =
      pref * a ^ q * ∑ k ∈ Finset.range r,
        (Nat.choose (r - 1) k : ℝ) * ((p - 1).factorial : ℝ) * (Nat.ascFactorial (p + q) (r - 1 - k) : ℝ) *
          (a ^ (-(q : ℤ)) * min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ)))) by
    simp only [C, Finset.sum_mul, Finset.mul_sum]
    have haq : a ^ q * a ^ (-(q : ℤ)) = 1 := by
      rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero q ha.ne')]
    set M := min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ)))
    refine Finset.sum_congr rfl fun k _ => ?_
    calc pref * ((Nat.choose (r - 1) k : ℝ) * ↑(p - 1).factorial * ↑((p + q).ascFactorial (r - 1 - k))) * M
        = pref * (a ^ q * a ^ (-(q : ℤ))) *
            ((Nat.choose (r - 1) k : ℝ) * ↑(p - 1).factorial * ↑((p + q).ascFactorial (r - 1 - k))) * M := by
            rw [haq, mul_one]
      _ = pref * a ^ q * ((Nat.choose (r - 1) k : ℝ) * ↑(p - 1).factorial * ↑((p + q).ascFactorial (r - 1 - k)) *
            (a ^ (-(q : ℤ)) * M)) := by ring]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by positivity)
  have hk_lt : k < r := Finset.mem_range.mp hk
  rw [norm_mul, norm_mul, Complex.norm_natCast, hinv_deriv (r - 1 - k) (p + q) a z hza_ne,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_zpow]
  have h1 : ‖iteratedDeriv k (fun u : ℂ => u ^ (p - 1)) z‖ ≤ ((p - 1).factorial : ℝ) * ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) :=
    (hpow_deriv k (p - 1) z).resolve_right hz0
  -- Key norm comparison: `‖z‖^{p-1-k} * ‖z+a‖^{-(p+q+r-1-k)} ≤ a^{-q} * min(...)`
  have hkey : ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) ≤
      a ^ (-(q : ℤ)) * min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ))) := by
    rw [mul_min_of_nonneg _ _ (zpow_pos ha _).le, le_min_iff]
    constructor
    · -- First bound: `‖z+a‖^{-(p+q)} ≤ a^{-(p+q)}` and `‖z+a‖^{-(r-1-k)} ≤ ‖z‖^{-(r-1-k)}`
      have hsplit : ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) =
          ‖z + (a : ℂ)‖ ^ (-((p + q : ℕ) : ℤ)) * ‖z + (a : ℂ)‖ ^ (-((r - 1 - k : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hza_pos.ne']; congr 1; omega
      have hle_a : ‖z + (a : ℂ)‖ ^ (-((p + q : ℕ) : ℤ)) ≤ a ^ (-((p + q : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos ha _) (pow_le_pow_left₀ ha.le (le_trans (le_max_right _ _) hza_ge) _)
      have hle_z : ‖z + (a : ℂ)‖ ^ (-((r - 1 - k : ℕ) : ℤ)) ≤ ‖z‖ ^ (-((r - 1 - k : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hz_pos _) (pow_le_pow_left₀ hz_pos.le (le_trans (le_max_left _ _) hza_ge) _)
      have hcomb : ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z‖ ^ (-((r - 1 - k : ℕ) : ℤ)) = ‖z‖ ^ ((p : ℤ) - r) := by
        rw [← zpow_add₀ hz_pos.ne']; congr 1; omega
      have ha_comb : a ^ (-((p + q : ℕ) : ℤ)) = a ^ (-(q : ℤ)) * a ^ (-(p : ℤ)) := by
        rw [← zpow_add₀ ha.ne']; congr 1; omega
      calc ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ))
          = ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * (‖z + (a : ℂ)‖ ^ (-((p + q : ℕ) : ℤ)) * ‖z + (a : ℂ)‖ ^ (-((r - 1 - k : ℕ) : ℤ))) := by
            rw [hsplit]
        _ ≤ ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * (a ^ (-((p + q : ℕ) : ℤ)) * ‖z‖ ^ (-((r - 1 - k : ℕ) : ℤ))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul hle_a hle_z (zpow_pos hza_pos _).le (zpow_pos ha _).le)
              (zpow_pos hz_pos _).le
        _ = (‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z‖ ^ (-((r - 1 - k : ℕ) : ℤ))) * a ^ (-((p + q : ℕ) : ℤ)) := by ring
        _ = a ^ (-(q : ℤ)) * (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) := by rw [hcomb, ha_comb]; ring
    · -- Second bound: `‖z+a‖^{-(p+q+r-1-k)} ≤ ‖z‖^{-(p+q+r-1-k)}`
      have hle_z : ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) ≤
          ‖z‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (pow_pos hz_pos _) (pow_le_pow_left₀ hz_pos.le (le_trans (le_max_left _ _) hza_ge) _)
      have hcomb : ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) =
          ‖z‖ ^ (-((q + r : ℕ) : ℤ)) := by
        rw [← zpow_add₀ hz_pos.ne']; congr 1; omega
      have ha_cancel : a ^ (-(q : ℤ)) * a ^ q = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero q ha.ne')]
      calc ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ))
          ≤ ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)) :=
            mul_le_mul_of_nonneg_left hle_z (zpow_pos hz_pos _).le
        _ = ‖z‖ ^ (-((q + r : ℕ) : ℤ)) := hcomb
        _ = a ^ (-(q : ℤ)) * (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ))) := by rw [← mul_assoc, ha_cancel, one_mul]
  calc (Nat.choose (r - 1) k : ℝ) * ‖iteratedDeriv k (fun u : ℂ => u ^ (p - 1)) z‖ *
        ((Nat.ascFactorial (p + q) (r - 1 - k) : ℝ) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ)))
      ≤ (Nat.choose (r - 1) k : ℝ) * (((p - 1).factorial : ℝ) * ‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k)) *
        ((Nat.ascFactorial (p + q) (r - 1 - k) : ℝ) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ))) := by
        gcongr
    _ = ((Nat.choose (r - 1) k : ℝ) * ((p - 1).factorial : ℝ) * (Nat.ascFactorial (p + q) (r - 1 - k) : ℝ)) *
        (‖z‖ ^ (((p - 1 : ℕ) : ℤ) - k) * ‖z + (a : ℂ)‖ ^ (-((p + q + (r - 1 - k) : ℕ) : ℤ))) := by ring
    _ ≤ ((Nat.choose (r - 1) k : ℝ) * ((p - 1).factorial : ℝ) * (Nat.ascFactorial (p + q) (r - 1 - k) : ℝ)) *
        (a ^ (-(q : ℤ)) * min (‖z‖ ^ ((p : ℤ) - r) * a ^ (-(p : ℤ))) (a ^ q * ‖z‖ ^ (-((q + r : ℕ) : ℤ)))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-! ### Leading expansions `(fct:pk-zero)`, `(fct:pk-inf)`, and imaginary bound on `z = it` -/

lemma phiKill_near_zero :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → ‖z‖ ≤ a / 2 →
      ‖phiKill a z - ((Nat.choose 15 8 : ℝ) : ℂ) * (z / a) ^ 8‖ ≤ C * (‖z‖ / a) ^ 9 := by
  -- Reduce to `a = 1` via `phiPQ_scale`: `‖w‖ ≤ 1/2`, `‖w + 1‖ ≥ 1/2`
  have h1 : ∃ C ≥ 0, ∀ {w : ℂ}, ‖w‖ ≤ 1 / 2 →
      ‖phiKill 1 w - ((Nat.choose 15 8 : ℝ) : ℂ) * w ^ 8‖ ≤ C * ‖w‖ ^ 9 := by
    -- `phiKill 1 w = ∑_{l=8}^{15} C(15, l) w^l / (w + 1)^15`
    -- `phiKill 1 w - C(15,8) w^8 = C(15,8) w^8 (1/(w+1)^15 - 1) + ∑_{l=9}^{15} C(15,l) w^l / (w+1)^15`
    -- Notice `1 - (w+1)^15 = -w * ∑_{k=0}^{14} (w+1)^k`, so `‖1/(w+1)^15 - 1‖ ≤ 2^15 * 15 * (3/2)^14 * ‖w‖`
    set C1 : ℝ := (Nat.choose 15 8 : ℝ) * (2 : ℝ) ^ 15 * 15 * (3 / 2 : ℝ) ^ 14
    set C2 : ℝ := ∑ l ∈ Finset.Ico 9 16, (Nat.choose 15 l : ℝ) * (2 : ℝ) ^ 15
    refine ⟨C1 + C2, by positivity, fun {w} hw => ?_⟩
    have hw1_ge : (1 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (-w)
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      rw [add_comm] at htri
      linarith
    have hw1_le : ‖w + 1‖ ≤ 3 / 2 := (norm_add_le w 1).trans (by rw [norm_one]; linarith)
    have hw1_ne : w + 1 ≠ 0 := norm_pos_iff.mp (by linarith)
    have hsplit : phiKill 1 w =
        ((Nat.choose 15 8 : ℝ) : ℂ) * (w / (w + 1)) ^ 8 * (1 / (w + 1)) ^ 7 +
        ∑ l ∈ Finset.Ico 9 16, ((Nat.choose 15 l : ℝ) : ℂ) * (w / (w + 1)) ^ l * (1 / (w + 1)) ^ (15 - l) := by
      unfold phiKill phiPQ
      simp only [Complex.ofReal_one]
      rw [show (8 : ℕ) + 8 = 16 by norm_num, show (16 : ℕ) - 1 = 15 by norm_num]
      rw [Finset.sum_eq_sum_Ico_succ_bot (by norm_num : 8 < 16)]
    rw [hsplit]
    have hterm8 : ((Nat.choose 15 8 : ℝ) : ℂ) * (w / (w + 1)) ^ 8 * (1 / (w + 1)) ^ 7 -
        ((Nat.choose 15 8 : ℝ) : ℂ) * w ^ 8 =
        ((Nat.choose 15 8 : ℝ) : ℂ) * w ^ 8 * (1 - (w + 1) ^ 15) / (w + 1) ^ 15 := by
      have : (w + 1) ^ 15 ≠ 0 := pow_ne_zero 15 hw1_ne
      field_simp
    have hsub_eq : ((Nat.choose 15 8 : ℝ) : ℂ) * (w / (w + 1)) ^ 8 * (1 / (w + 1)) ^ 7 +
        (∑ l ∈ Finset.Ico 9 16, ((Nat.choose 15 l : ℝ) : ℂ) * (w / (w + 1)) ^ l * (1 / (w + 1)) ^ (15 - l)) -
        ((Nat.choose 15 8 : ℝ) : ℂ) * w ^ 8 =
        ((Nat.choose 15 8 : ℝ) : ℂ) * w ^ 8 * (1 - (w + 1) ^ 15) / (w + 1) ^ 15 +
        ∑ l ∈ Finset.Ico 9 16, ((Nat.choose 15 l : ℝ) : ℂ) * w ^ l / (w + 1) ^ 15 := by
      have hsum_eq : ∑ l ∈ Finset.Ico 9 16, ((Nat.choose 15 l : ℝ) : ℂ) * (w / (w + 1)) ^ l * (1 / (w + 1)) ^ (15 - l) =
          ∑ l ∈ Finset.Ico 9 16, ((Nat.choose 15 l : ℝ) : ℂ) * w ^ l / (w + 1) ^ 15 := by
        refine Finset.sum_congr rfl fun l hl => ?_
        have hl15 : l ≤ 15 := by have := (Finset.mem_Ico.mp hl).2; omega
        have hpow15 : (w + 1) ^ l * (w + 1) ^ (15 - l) = (w + 1) ^ 15 := by
          rw [← pow_add]; congr 1; omega
        rw [div_pow, div_pow, one_pow]
        field_simp [hw1_ne]
        rw [mul_assoc _ ((w + 1) ^ l), hpow15]
      rw [hsum_eq]; linear_combination hterm8
    rw [hsub_eq]
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · -- Bound `‖C(15,8) w^8 (1 - (w+1)^15) / (w+1)^15‖ ≤ C1 ‖w‖^9`
      have hgeom : (w + 1) ^ 15 - 1 = w * ∑ k ∈ Finset.range 15, (w + 1) ^ k := by
        have := geom_sum_mul (w + 1) 15
        simp only [add_sub_cancel_right] at this
        linear_combination this.symm
      have hdiff15 : ‖1 - (w + 1) ^ 15‖ ≤ 15 * (3 / 2 : ℝ) ^ 14 * ‖w‖ := by
        rw [norm_sub_rev, hgeom, norm_mul]
        have hsum_bd : ‖∑ k ∈ Finset.range 15, (w + 1) ^ k‖ ≤ 15 * (3 / 2 : ℝ) ^ 14 := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ k ∈ Finset.range 15, ‖(w + 1) ^ k‖
              ≤ ∑ _k ∈ Finset.range 15, (3 / 2 : ℝ) ^ 14 := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_pow]
                have hk14 : k ≤ 14 := by have := Finset.mem_range.mp hk; omega
                exact (pow_le_pow_left₀ (norm_nonneg _) hw1_le k).trans
                  (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hk14)
            _ = 15 * (3 / 2 : ℝ) ^ 14 := by simp
        nlinarith [norm_nonneg w]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), norm_pow, norm_pow]
      have hinv15 : (1 / ‖w + 1‖ ^ 15) ≤ (2 : ℝ) ^ 15 := by
        rw [one_div, inv_le_comm₀ (pow_pos (by linarith) 15) (by positivity)]
        have : (1 / 2 : ℝ) ^ 15 ≤ ‖w + 1‖ ^ 15 := pow_le_pow_left₀ (by norm_num) hw1_ge 15
        norm_num at this ⊢; linarith
      calc (Nat.choose 15 8 : ℝ) * ‖w‖ ^ 8 * ‖1 - (w + 1) ^ 15‖ / ‖w + 1‖ ^ 15
          = (Nat.choose 15 8 : ℝ) * ‖w‖ ^ 8 * ‖1 - (w + 1) ^ 15‖ * (1 / ‖w + 1‖ ^ 15) := by ring
        _ ≤ (Nat.choose 15 8 : ℝ) * ‖w‖ ^ 8 * (15 * (3 / 2 : ℝ) ^ 14 * ‖w‖) * (2 : ℝ) ^ 15 := by
            gcongr
        _ = C1 * ‖w‖ ^ 9 := by simp only [C1]; ring
    · -- Bound `‖∑_{l=9}^{15} C(15,l) w^l / (w+1)^15‖ ≤ C2 ‖w‖^9`
      refine (norm_sum_le _ _).trans ?_
      rw [show C2 * ‖w‖ ^ 9 = ∑ l ∈ Finset.Ico 9 16, (Nat.choose 15 l : ℝ) * (2 : ℝ) ^ 15 * ‖w‖ ^ 9 by
        simp only [C2, Finset.sum_mul]]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl9 : 9 ≤ l := (Finset.mem_Ico.mp hl).1
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), norm_pow, norm_pow]
      have hinv15 : (1 / ‖w + 1‖ ^ 15) ≤ (2 : ℝ) ^ 15 := by
        rw [one_div, inv_le_comm₀ (pow_pos (by linarith) 15) (by positivity)]
        have : (1 / 2 : ℝ) ^ 15 ≤ ‖w + 1‖ ^ 15 := pow_le_pow_left₀ (by norm_num) hw1_ge 15
        norm_num at this ⊢; linarith
      have hw_pow : ‖w‖ ^ l ≤ ‖w‖ ^ 9 :=
        pow_le_pow_of_le_one (norm_nonneg w) (hw.trans (by norm_num)) hl9
      calc (Nat.choose 15 l : ℝ) * ‖w‖ ^ l / ‖w + 1‖ ^ 15
          = (Nat.choose 15 l : ℝ) * ‖w‖ ^ l * (1 / ‖w + 1‖ ^ 15) := by ring
        _ ≤ (Nat.choose 15 l : ℝ) * ‖w‖ ^ 9 * (2 : ℝ) ^ 15 := by gcongr
        _ = (Nat.choose 15 l : ℝ) * (2 : ℝ) ^ 15 * ‖w‖ ^ 9 := by ring
  obtain ⟨C, hC, hbd⟩ := h1
  refine ⟨C, hC, fun {a z} ha hz => ?_⟩
  rw [phiKill, phiPQ_scale ha]
  have hw : ‖z / (a : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_le_iff₀ ha]
    linarith
  have := hbd hw
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at this
  exact this

/-- Near-infinity expansion `(fct:pk-inf)`: `1 - φ_kill(z; a) = C(15, 7)(a/z)^8 + O((a/|z|)^9)`
for `|z| ≥ 2a`, `Re z ≥ 0`. Follows from `phiKill_near_zero` via the inversion symmetry
`1 - φ_kill(z; a) = φ_kill(a; z) = φ_kill(a²/z; a)`! -/
lemma one_sub_phiKill_near_inf :
    ∃ C ≥ 0, ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re → 2 * a ≤ ‖z‖ →
      ‖(1 - phiKill a z) - ((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / z) ^ 8‖ ≤ C * (a / ‖z‖) ^ 9 := by
  obtain ⟨C, hC, hbd⟩ := phiKill_near_zero
  refine ⟨C, hC, fun {a z} ha hz h2a => ?_⟩
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hza : z + (a : ℂ) ≠ 0 := add_ofReal_ne_zero_of_re_nonneg ha hz
  -- Exact inversion symmetry: `1 - phiKill a z = phiKill 1 (a / z)`!
  have hsym : 1 - phiKill a z = phiKill 1 ((a : ℂ) / z) := by
    unfold phiKill
    rw [one_sub_phiPQ (by norm_num : 1 ≤ 8) hza]
    unfold phiPQ
    simp only [Complex.ofReal_one]
    rw [show (8 : ℕ) + 8 = 16 by norm_num, show (16 : ℕ) - 1 = 15 by norm_num]
    refine Finset.sum_nbij (fun l => 15 - l) ?_ ?_ ?_ ?_
    · intro l hl; rw [Finset.mem_range] at hl; rw [Finset.mem_Ico]; omega
    · intro l₁ hl₁ l₂ hl₂ heq
      have h1 : l₁ < 8 := Finset.mem_range.mp hl₁
      have h2 : l₂ < 8 := Finset.mem_range.mp hl₂
      dsimp only at heq; omega
    · intro m hm
      have hm' := Finset.mem_Ico.mp hm
      exact ⟨15 - m, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩
    · intro l hl
      rw [Finset.mem_range] at hl
      have hch : Nat.choose 15 l = Nat.choose 15 (15 - l) := (Nat.choose_symm (by omega)).symm
      rw [hch, show 15 - (15 - l) = l by omega]
      have hza_div : (a : ℂ) / z + 1 ≠ 0 := by
        intro h; apply hza; field_simp [hz0] at h; linear_combination h
      have h1 : z / (z + (a : ℂ)) = 1 / ((a : ℂ) / z + 1) := by
        rw [div_add_one hz0, one_div_div, add_comm]
      have h2 : (a : ℂ) / (z + (a : ℂ)) = ((a : ℂ) / z) / ((a : ℂ) / z + 1) := by
        rw [div_add_one hz0, div_div_div_cancel_right₀ hz0, add_comm]
      rw [h1, h2]; ring
  rw [hsym, show Nat.choose 15 7 = Nat.choose 15 8 from (Nat.choose_symm (by norm_num : 7 ≤ 15)).symm]
  have hw : ‖(a : ℂ) / z‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, div_le_iff₀ (norm_pos_iff.mpr hz0)]
    linarith
  have hres := hbd (a := 1) (z := (a : ℂ) / z) one_pos (by linarith)
  simp only [Complex.ofReal_one, div_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hres
  exact hres

/-- Imaginary-part bound on `z = it`: `|Im φ_kill(it; a)| ≤ C min((|t|/a)^9, (a/|t|)^8)`
(in fact `(a/|t|)^9` at infinity). -/
lemma abs_im_phiKill_le :
    ∃ C ≥ 0, ∀ {a t : ℝ}, 0 < a → t ≠ 0 →
      |(phiKill a ((t : ℂ) * Complex.I)).im| ≤ C * min ((|t| / a) ^ 9) ((a / |t|) ^ 8) := by
  obtain ⟨C0, hC0, h0⟩ := phiKill_near_zero
  obtain ⟨Cinf, hCinf, hinf⟩ := one_sub_phiKill_near_inf
  obtain ⟨Cb, hCb, hb⟩ := norm_phiPQ_le 8 8
  set C : ℝ := max (max C0 Cinf) (Cb * 2 ^ 9)
  refine ⟨C, by positivity, fun {a t} ha ht => ?_⟩
  have hre0 : (0 : ℝ) ≤ ((t : ℂ) * Complex.I).re := by simp
  have hnorm_it : ‖(t : ℂ) * Complex.I‖ = |t| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have habs_pos : 0 < |t| := abs_pos.mpr ht
  -- Case 1: `|t| ≤ a / 2`
  by_cases hsmall : |t| ≤ a / 2
  · have hreal8 : (((Nat.choose 15 8 : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / (a : ℂ)) ^ 8).im = 0 := by
      have hi8 : Complex.I ^ 8 = 1 := by
        calc Complex.I ^ 8 = (Complex.I ^ 2) ^ 4 := by ring
          _ = (-1) ^ 4 := by rw [Complex.I_sq]
          _ = 1 := by norm_num
      have : ((Nat.choose 15 8 : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / (a : ℂ)) ^ 8 =
          (((Nat.choose 15 8 : ℝ) * (t / a) ^ 8 : ℝ) : ℂ) := by
        rw [mul_div_right_comm, mul_pow, hi8, mul_one]; push_cast; rfl
      rw [this, Complex.ofReal_im]
    have him_le : |(phiKill a ((t : ℂ) * Complex.I)).im| ≤
        ‖phiKill a ((t : ℂ) * Complex.I) - ((Nat.choose 15 8 : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / (a : ℂ)) ^ 8‖ := by
      have := Complex.abs_im_le_norm (phiKill a ((t : ℂ) * Complex.I) -
        ((Nat.choose 15 8 : ℝ) : ℂ) * (((t : ℂ) * Complex.I) / (a : ℂ)) ^ 8)
      rwa [Complex.sub_im, hreal8, sub_zero] at this
    have hbd0 := h0 ha (by rw [hnorm_it]; exact hsmall)
    rw [hnorm_it] at hbd0
    have hmin : min ((|t| / a) ^ 9) ((a / |t|) ^ 8) = (|t| / a) ^ 9 := by
      refine min_eq_left ?_
      have hle1 : (|t| / a) ^ 9 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one ha).mpr (by linarith))
      have hge1 : 1 ≤ (a / |t|) ^ 8 := one_le_pow₀ ((one_le_div habs_pos).mpr (by linarith))
      linarith
    rw [hmin]
    exact (him_le.trans hbd0).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (by positivity))
  -- Case 2: `2 * a ≤ |t|`
  by_cases hlarge : 2 * a ≤ |t|
  · have hreal8 : (((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / ((t : ℂ) * Complex.I)) ^ 8).im = 0 := by
      have hi8 : Complex.I ^ 8 = 1 := by
        calc Complex.I ^ 8 = (Complex.I ^ 2) ^ 4 := by ring
          _ = (-1) ^ 4 := by rw [Complex.I_sq]
          _ = 1 := by norm_num
      have : ((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / ((t : ℂ) * Complex.I)) ^ 8 =
          (((Nat.choose 15 7 : ℝ) * (a / t) ^ 8 : ℝ) : ℂ) := by
        rw [div_pow, mul_pow, hi8, mul_one, ← div_pow]; push_cast; rfl
      rw [this, Complex.ofReal_im]
    have him_le : |(phiKill a ((t : ℂ) * Complex.I)).im| ≤
        ‖(1 - phiKill a ((t : ℂ) * Complex.I)) -
          ((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / ((t : ℂ) * Complex.I)) ^ 8‖ := by
      have := Complex.abs_im_le_norm ((1 - phiKill a ((t : ℂ) * Complex.I)) -
        ((Nat.choose 15 7 : ℝ) : ℂ) * ((a : ℂ) / ((t : ℂ) * Complex.I)) ^ 8)
      rw [Complex.sub_im, Complex.sub_im, Complex.one_im, zero_sub, hreal8, sub_zero, abs_neg] at this
      exact this
    have hbdinf := hinf ha hre0 (by rw [hnorm_it]; exact hlarge)
    rw [hnorm_it] at hbdinf
    have h9_le_8 : (a / |t|) ^ 9 ≤ (a / |t|) ^ 8 :=
      pow_le_pow_of_le_one (by positivity) ((div_le_one habs_pos).mpr (by linarith)) (by norm_num)
    have hmin : min ((|t| / a) ^ 9) ((a / |t|) ^ 8) = (a / |t|) ^ 8 := by
      refine min_eq_right ?_
      have hle1 : (a / |t|) ^ 8 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one habs_pos).mpr (by linarith))
      have hge1 : 1 ≤ (|t| / a) ^ 9 := one_le_pow₀ ((one_le_div ha).mpr (by linarith))
      linarith
    rw [hmin]
    calc |(phiKill a ((t : ℂ) * Complex.I)).im|
        ≤ Cinf * (a / |t|) ^ 9 := him_le.trans hbdinf
      _ ≤ Cinf * (a / |t|) ^ 8 := mul_le_mul_of_nonneg_left h9_le_8 hCinf
      _ ≤ C * (a / |t|) ^ 8 := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) (by positivity)
  -- Case 3: `a / 2 < |t| < 2 * a`
  · have h1 : a / 2 < |t| := lt_of_not_ge hsmall
    have h2 : |t| < 2 * a := lt_of_not_ge hlarge
    have him_le : |(phiKill a ((t : ℂ) * Complex.I)).im| ≤ Cb := by
      have := (Complex.abs_im_le_norm _).trans (hb ha hre0)
      exact this.trans (by simpa using mul_le_mul_of_nonneg_left (min_le_right ((‖(t : ℂ) * Complex.I‖ / a) ^ 8) 1) hCb)
    have hmin_ge : (1 / 2 : ℝ) ^ 9 ≤ min ((|t| / a) ^ 9) ((a / |t|) ^ 8) := by
      rw [le_min_iff]
      constructor
      · exact pow_le_pow_left₀ (by norm_num) ((le_div_iff₀ ha).mpr (by linarith)) 9
      · calc (1 / 2 : ℝ) ^ 9 ≤ (1 / 2 : ℝ) ^ 8 := by norm_num
          _ ≤ (a / |t|) ^ 8 := pow_le_pow_left₀ (by norm_num) ((le_div_iff₀ habs_pos).mpr (by linarith)) 8
    calc |(phiKill a ((t : ℂ) * Complex.I)).im|
        ≤ Cb := him_le
      _ = (Cb * 2 ^ 9) * (1 / 2 : ℝ) ^ 9 := by ring
      _ ≤ C * min ((|t| / a) ^ 9) ((a / |t|) ^ 8) :=
          mul_le_mul (le_max_right _ _) hmin_ge (by positivity) (by positivity)

/-! ### Part (2): Exact Cauchy moment vanishing `(fct:pk-cauchy)` -/

/-- Elementary FTC integral: `∫_{-∞}^∞ (i s + 1)^{-d} ds = 0` for every integer `d ≥ 2`. -/
lemma integral_inv_I_mul_add_one_pow {d : ℕ} (hd : 2 ≤ d) :
    ∫ s : ℝ, ((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ)) = 0 := by
  let F : ℝ → ℂ := fun s =>
    ((Complex.I * (1 - (d : ℂ)))⁻¹) * ((s : ℂ) * Complex.I + 1) ^ (1 - (d : ℤ))
  have hne : ∀ s : ℝ, (s : ℂ) * Complex.I + 1 ≠ 0 := fun s h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Complex.one_re, zero_add,
      Complex.zero_re] at this
    norm_num at this
  have hden_ne : Complex.I * (1 - (d : ℂ)) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re, Complex.zero_re] at hre
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hderiv : ∀ s : ℝ, HasDerivAt F (((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ))) s := by
    intro s
    have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I + 1) Complex.I s := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
      simpa using (h1.mul_const Complex.I).add_const (1 : ℂ)
    have hpow : HasDerivAt (fun u : ℝ => ((u : ℂ) * Complex.I + 1) ^ (1 - (d : ℤ)))
        (((1 - (d : ℤ) : ℤ) : ℂ) * ((s : ℂ) * Complex.I + 1) ^ ((1 - (d : ℤ)) - 1) * Complex.I) s := by
      simpa [Function.comp_def] using
        (hasDerivAt_zpow (1 - (d : ℤ)) ((s : ℂ) * Complex.I + 1) (Or.inl (hne s))).comp s hlin
    have hF := hpow.const_mul (Complex.I * (1 - (d : ℂ)))⁻¹
    refine hF.congr_deriv ?_
    have hexp : (1 - (d : ℤ)) - 1 = -(d : ℤ) := by omega
    rw [hexp]
    have hcast : ((1 - (d : ℤ) : ℤ) : ℂ) = 1 - (d : ℂ) := by push_cast; rfl
    rw [hcast]
    have hd1 : (1 : ℂ) - (d : ℂ) ≠ 0 := right_ne_zero_of_mul hden_ne
    field_simp [Complex.I_ne_zero, hd1]
  have hnorm_bound : ∀ s : ℝ, ‖((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ))‖ ≤ (1 + s ^ 2)⁻¹ := by
    intro s
    have hnsq : ‖(s : ℂ) * Complex.I + 1‖ ^ 2 = 1 + s ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Complex.one_re, zero_add,
        Complex.add_im, Complex.mul_im, Complex.one_im, add_zero]
      ring
    have hge1 : 1 ≤ ‖(s : ℂ) * Complex.I + 1‖ := by
      exact le_of_sq_le_sq (by rw [hnsq]; nlinarith [sq_nonneg s]) (norm_nonneg _)
    rw [norm_zpow, zpow_neg, zpow_natCast]
    calc (‖(s : ℂ) * Complex.I + 1‖ ^ d)⁻¹
        ≤ (‖(s : ℂ) * Complex.I + 1‖ ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_right₀ hge1 hd)
      _ = (1 + s ^ 2)⁻¹ := by rw [hnsq]
  have hint : Integrable (fun s : ℝ => ((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ))) := by
    have hcont : Continuous (fun s : ℝ => ((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ))) := by
      have : (fun s : ℝ => ((s : ℂ) * Complex.I + 1) ^ (-(d : ℤ))) =
          fun s : ℝ => (((s : ℂ) * Complex.I + 1) ^ d)⁻¹ := by ext s; rw [zpow_neg, zpow_natCast]
      rw [this]
      exact (((Complex.continuous_ofReal.mul continuous_const).add continuous_const).pow d).inv₀
        fun s => pow_ne_zero d (hne s)
    exact integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm_bound)
  have hF_tend : Tendsto F atTop (𝓝 0) ∧ Tendsto F atBot (𝓝 0) := by
    have hF_norm : ∀ s : ℝ, ‖F s‖ ≤ 2 * ‖(Complex.I * (1 - (d : ℂ)))⁻¹‖ / (1 + |s|) := by
      intro s
      simp only [F, norm_mul, norm_zpow]
      have hnsq : ‖(s : ℂ) * Complex.I + 1‖ ^ 2 = 1 + s ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hge : 1 ≤ ‖(s : ℂ) * Complex.I + 1‖ :=
        le_of_sq_le_sq (by rw [hnsq]; nlinarith [sq_nonneg s]) (norm_nonneg _)
      have hge_s : (1 + |s|) / 2 ≤ ‖(s : ℂ) * Complex.I + 1‖ := by
        have hsq : ((1 + |s|) / 2) ^ 2 ≤ 1 + s ^ 2 := by
          have : |s| ^ 2 = s ^ 2 := sq_abs s
          nlinarith [sq_nonneg (|s| - 1)]
        exact le_of_sq_le_sq (by rw [hnsq]; exact hsq) (norm_nonneg _)
      have hexp : 1 - (d : ℤ) = -((d - 1 : ℕ) : ℤ) := by omega
      rw [hexp, zpow_neg, zpow_natCast]
      have hd1 : 1 ≤ d - 1 := by omega
      have hpow : ‖(s : ℂ) * Complex.I + 1‖ ≤ ‖(s : ℂ) * Complex.I + 1‖ ^ (d - 1) := by
        simpa using pow_le_pow_right₀ hge hd1
      have hinv : (‖(s : ℂ) * Complex.I + 1‖ ^ (d - 1))⁻¹ ≤ 2 / (1 + |s|) := by
        calc (‖(s : ℂ) * Complex.I + 1‖ ^ (d - 1))⁻¹
            ≤ ‖(s : ℂ) * Complex.I + 1‖⁻¹ := inv_anti₀ (by linarith) hpow
          _ ≤ ((1 + |s|) / 2)⁻¹ := inv_anti₀ (by positivity) hge_s
          _ = 2 / (1 + |s|) := by rw [inv_div]
      calc ‖(Complex.I * (1 - (d : ℂ)))⁻¹‖ * (‖(s : ℂ) * Complex.I + 1‖ ^ (d - 1))⁻¹
          ≤ ‖(Complex.I * (1 - (d : ℂ)))⁻¹‖ * (2 / (1 + |s|)) :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = 2 * ‖(Complex.I * (1 - (d : ℂ)))⁻¹‖ / (1 + |s|) := by ring
    have htend_of : ∀ {l : Filter ℝ}, Tendsto (fun s : ℝ => |s|) l atTop → Tendsto F l (𝓝 0) := by
      intro l hl
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun s => norm_nonneg _) hF_norm ?_
      have h1 : Tendsto (fun s : ℝ => 1 + |s|) l atTop :=
        tendsto_atTop_add_const_left l 1 hl
      exact tendsto_const_nhds.div_atTop h1
    exact ⟨htend_of (tendsto_abs_atTop_atTop), htend_of (tendsto_abs_atBot_atTop)⟩
  have := integral_of_hasDerivAt_of_tendsto hderiv hint hF_tend.2 hF_tend.1
  simpa using this

/-- Integral of `(is)^m / (is + 1)^n` over `ℝ` is `0` whenever `m + 2 ≤ n`. -/
lemma integral_I_pow_div_add_one_pow {m n : ℕ} (hmn : m + 2 ≤ n) :
    ∫ s : ℝ, ((s : ℂ) * Complex.I) ^ m / ((s : ℂ) * Complex.I + 1) ^ n = 0 := by
  have hexpand : ∀ z : ℂ, z + 1 ≠ 0 →
      z ^ m / (z + 1) ^ n =
        ∑ r ∈ Finset.range (m + 1),
          ((Nat.choose m r : ℝ) : ℂ) * (-1 : ℂ) ^ (m - r) * (z + 1) ^ (-((n - r : ℕ) : ℤ)) := by
    intro z hz
    have hpow : z ^ m = ∑ r ∈ Finset.range (m + 1),
        (z + 1) ^ r * (-1 : ℂ) ^ (m - r) * (Nat.choose m r : ℂ) := by
      have h := add_pow (z + 1) (-1 : ℂ) m
      simp only [add_neg_cancel_right] at h
      exact h
    rw [hpow, Finset.sum_div]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_le : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hnr : r + (n - r) = n := by omega
    rw [zpow_neg, zpow_natCast, ← hnr, pow_add]
    have hr_ne : (z + 1) ^ r ≠ 0 := pow_ne_zero r hz
    have hnr_ne : (z + 1) ^ (n - r) ≠ 0 := pow_ne_zero (n - r) hz
    push_cast
    field_simp [hr_ne, hnr_ne]
    rw [Nat.add_sub_cancel_left]
  have hne : ∀ s : ℝ, (s : ℂ) * Complex.I + 1 ≠ 0 := fun s h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Complex.one_re, zero_add,
      Complex.zero_re] at this
    norm_num at this
  have hfun : (fun s : ℝ => ((s : ℂ) * Complex.I) ^ m / ((s : ℂ) * Complex.I + 1) ^ n) =
      fun s : ℝ => ∑ r ∈ Finset.range (m + 1),
        ((Nat.choose m r : ℝ) : ℂ) * (-1 : ℂ) ^ (m - r) * ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ)) :=
    funext fun s => hexpand _ (hne s)
  rw [hfun]
  have hint_r : ∀ r ∈ Finset.range (m + 1),
      Integrable (fun s : ℝ => ((Nat.choose m r : ℝ) : ℂ) * (-1 : ℂ) ^ (m - r) *
        ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ))) := by
    intro r hr
    have hr_le : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hd : 2 ≤ n - r := by omega
    refine Integrable.const_mul ?_ _
    have hcont : Continuous (fun s : ℝ => ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ))) := by
      have : (fun s : ℝ => ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ))) =
          fun s : ℝ => (((s : ℂ) * Complex.I + 1) ^ (n - r))⁻¹ := by ext s; rw [zpow_neg, zpow_natCast]
      rw [this]
      exact (((Complex.continuous_ofReal.mul continuous_const).add continuous_const).pow _).inv₀
        fun s => pow_ne_zero _ (hne s)
    refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => ?_)
    have hnsq : ‖(s : ℂ) * Complex.I + 1‖ ^ 2 = 1 + s ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hge1 : 1 ≤ ‖(s : ℂ) * Complex.I + 1‖ :=
      le_of_sq_le_sq (by rw [hnsq]; nlinarith [sq_nonneg s]) (norm_nonneg _)
    rw [norm_zpow, zpow_neg, zpow_natCast]
    calc (‖(s : ℂ) * Complex.I + 1‖ ^ (n - r))⁻¹
        ≤ (‖(s : ℂ) * Complex.I + 1‖ ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_right₀ hge1 hd)
      _ = (1 + s ^ 2)⁻¹ := by rw [hnsq]
  have hsum_int : ∀ (S : Finset ℕ), (∀ r ∈ S, r ≤ m) →
      Integrable (fun s : ℝ => ∑ r ∈ S,
        ((Nat.choose m r : ℝ) : ℂ) * (-1 : ℂ) ^ (m - r) * ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ))) ∧
      ∫ s : ℝ, (∑ r ∈ S,
        ((Nat.choose m r : ℝ) : ℂ) * (-1 : ℂ) ^ (m - r) * ((s : ℂ) * Complex.I + 1) ^ (-((n - r : ℕ) : ℤ))) = 0 := by
    intro S hS
    induction S using Finset.cons_induction with
    | empty => exact ⟨by simp, by simp⟩
    | cons r S hrS ih =>
      have hr_le : r ≤ m := hS r (Finset.mem_cons_self r S)
      have hS' : ∀ r' ∈ S, r' ≤ m := fun r' hr' => hS r' (Finset.mem_cons_of_mem hr')
      have h1 := hint_r r (Finset.mem_range.mpr (by omega))
      have h2 := ih hS'
      simp_rw [Finset.sum_cons]
      refine ⟨h1.add h2.1, ?_⟩
      rw [integral_add h1 h2.1, h2.2, add_zero, integral_const_mul,
        integral_inv_I_mul_add_one_pow (by omega : 2 ≤ n - r), mul_zero]
  exact (hsum_int (Finset.range (m + 1)) fun r hr => Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)).2

/-- Helper: for an even integrable function `f : ℝ → ℝ`, `∫_{t>0} f t = (1/2) ∫_ℝ f t`. -/
lemma setIntegral_Ioi_eq_half_of_even {f : ℝ → ℝ} (hf : Integrable f) (heven : ∀ t, f (-t) = f t) :
    ∫ t in Ioi (0 : ℝ), f t = (1 / 2) * ∫ t : ℝ, f t := by
  have hsplit : ∫ t : ℝ, f t = (∫ t in Iic (0 : ℝ), f t) + (∫ t in Ioi (0 : ℝ), f t) := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn hf.integrableOn,
      Iic_union_Ioi, setIntegral_univ]
  have hneg : ∫ t in Iic (0 : ℝ), f t = ∫ t in Ioi (0 : ℝ), f t := by
    have hcomp := integral_comp_neg_Ioi (c := (0 : ℝ)) (f := f)
    simp only [neg_zero] at hcomp
    rw [← hcomp]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => heven t
  linarith

/-- **Lemma `fct:phikill` (2), first identity**:
`∫_0^∞ Re(φ_{p,q}(it; a)) / t^{2j} dt = 0` for `1 ≤ j`, `2j ≤ p`, `q ≥ 1`, `a > 0`. -/
theorem phiPQ_moment_neg {p q j : ℕ} (hq : 1 ≤ q) (hj : 1 ≤ j) (h2j : 2 * j ≤ p)
    {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j) = 0 := by
  -- Reduce to `a = 1` by scaling `t = a * s`
  have hcov : ∫ t in Ioi (0 : ℝ), (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j) =
      a ^ (1 - (2 * j : ℤ)) * ∫ s in Ioi (0 : ℝ), (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j) := by
    have h1 := integral_comp_mul_left_Ioi
      (fun t : ℝ => (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) (0 : ℝ) ha
    simp only [mul_zero, smul_eq_mul] at h1
    have h2 : ∫ s in Ioi (0 : ℝ), (phiPQ p q a (((a * s : ℝ) : ℂ) * Complex.I)).re / (a * s) ^ (2 * j) =
        a ^ (-(2 * j : ℤ)) * ∫ s in Ioi (0 : ℝ), (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [phiPQ_scale ha]
      have harg : ((a * s : ℝ) : ℂ) * Complex.I / (a : ℂ) = (s : ℂ) * Complex.I := by
        have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
        push_cast; field_simp
      rw [harg, mul_pow, zpow_neg, show a ^ (2 * (j : ℤ)) = a ^ (2 * j) by norm_cast]; ring
    rw [h2] at h1
    have hpow : a * a ^ (-(2 * j : ℤ)) = a ^ (1 - (2 * j : ℤ)) := by
      rw [show (1 : ℤ) - (2 * j : ℤ) = 1 + -(2 * j : ℤ) by omega, zpow_add₀ ha.ne', zpow_one]
    have ha_ne : a ≠ 0 := ha.ne'
    calc ∫ t in Ioi (0 : ℝ), (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)
        = a * (a⁻¹ * ∫ t in Ioi (0 : ℝ), (phiPQ p q a ((t : ℂ) * Complex.I)).re / t ^ (2 * j)) := by
          rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]
      _ = a * (a ^ (-(2 * j : ℤ)) * ∫ s in Ioi (0 : ℝ), (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j)) := by
          rw [← h1]
      _ = a ^ (1 - (2 * j : ℤ)) * ∫ s in Ioi (0 : ℝ), (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j) := by
          rw [← mul_assoc, hpow]
  rw [hcov]
  suffices h0 : ∫ s in Ioi (0 : ℝ), (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j) = 0 by
    rw [h0, mul_zero]
  -- Write `(phiPQ p q 1 (is)) / (is)^{2j} = ∑_{l=p}^{p+q-1} C(n, l) (is)^{l-2j} / (is+1)^n`
  set n : ℕ := p + q - 1
  have hne : ∀ s : ℝ, (s : ℂ) * Complex.I + 1 ≠ 0 := fun s h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Complex.one_re, zero_add,
      Complex.zero_re] at this
    norm_num at this
  let G : ℝ → ℂ := fun s => ∑ l ∈ Finset.Ico p (p + q),
    ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l - 2 * j) / ((s : ℂ) * Complex.I + 1) ^ n)
  have hG_eq : ∀ s : ℝ, s ≠ 0 →
      (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j) = ((-1 : ℝ) ^ j) * (G s).re := by
    intro s hs
    have hpowI : ((s : ℂ) * Complex.I) ^ (2 * j) = ((((-1 : ℝ) ^ j * s ^ (2 * j) : ℝ)) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]; push_cast; ring
    have hmul : phiPQ p q 1 ((s : ℂ) * Complex.I) = ((s : ℂ) * Complex.I) ^ (2 * j) * G s := by
      unfold phiPQ
      simp only [Complex.ofReal_one, G, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlp : p ≤ l := (Finset.mem_Ico.mp hl).1
      have hln : l ≤ n := by have := (Finset.mem_Ico.mp hl).2; omega
      have h2jl : 2 * j + (l - 2 * j) = l := by omega
      have hln' : l + (n - l) = n := by omega
      have hpow_den : ((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l) =
          ((s : ℂ) * Complex.I + 1) ^ n := by rw [← pow_add, hln']
      have hpow_num : ((s : ℂ) * Complex.I) ^ (2 * j) * ((s : ℂ) * Complex.I) ^ (l - 2 * j) =
          ((s : ℂ) * Complex.I) ^ l := by rw [← pow_add, h2jl]
      rw [div_pow, div_pow, one_pow]
      change ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ l / ((s : ℂ) * Complex.I + 1) ^ l) *
          (1 / ((s : ℂ) * Complex.I + 1) ^ (n - l)) = _
      field_simp [hne s]
      calc ((Nat.choose n l : ℝ) : ℂ) * ((s : ℂ) * Complex.I) ^ l * ((s : ℂ) * Complex.I + 1) ^ n
          = ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (2 * j) * ((s : ℂ) * Complex.I) ^ (l - 2 * j)) *
              (((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l)) := by
              rw [hpow_num, hpow_den]
        _ = ((Nat.choose n l : ℝ) : ℂ) * ((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l) *
              ((s : ℂ) * Complex.I) ^ (2 * j) * ((s : ℂ) * Complex.I) ^ (l - 2 * j) := by ring
    have hre := congrArg Complex.re hmul
    rw [hpowI, Complex.re_ofReal_mul] at hre
    have hs2j : s ^ (2 * j) ≠ 0 := pow_ne_zero _ hs
    rw [hre]
    field_simp [hs2j]
  -- `G` is integrable on `ℝ` and `∫_ℝ G = 0`
  have hG_int_and_zero : Integrable G ∧ ∫ s : ℝ, G s = 0 := by
    have hterm_int : ∀ l ∈ Finset.Ico p (p + q),
        Integrable (fun s : ℝ => ((Nat.choose n l : ℝ) : ℂ) *
          (((s : ℂ) * Complex.I) ^ (l - 2 * j) / ((s : ℂ) * Complex.I + 1) ^ n)) := by
      intro l hl
      have hln : l ≤ n := by have := (Finset.mem_Ico.mp hl).2; omega
      have hdeg : (l - 2 * j) + 2 ≤ n := by omega
      refine Integrable.const_mul ?_ _
      have hcont : Continuous (fun s : ℝ => ((s : ℂ) * Complex.I) ^ (l - 2 * j) / ((s : ℂ) * Complex.I + 1) ^ n) :=
        ((Complex.continuous_ofReal.mul continuous_const).pow _).div
          (((Complex.continuous_ofReal.mul continuous_const).add continuous_const).pow _)
          fun s => pow_ne_zero _ (hne s)
      refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      have hnsq : ‖(s : ℂ) * Complex.I + 1‖ ^ 2 = 1 + s ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hge1 : 1 ≤ ‖(s : ℂ) * Complex.I + 1‖ :=
        le_of_sq_le_sq (by rw [hnsq]; nlinarith [sq_nonneg s]) (norm_nonneg _)
      have hle_den : ‖(s : ℂ) * Complex.I‖ ≤ ‖(s : ℂ) * Complex.I + 1‖ := by
        have h1 : ‖(s : ℂ) * Complex.I‖ ^ 2 = s ^ 2 := by rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, sq_abs]
        exact le_of_sq_le_sq (by rw [h1, hnsq]; linarith) (norm_nonneg _)
      rw [norm_div, norm_pow, norm_pow]
      have hsplit : ‖(s : ℂ) * Complex.I + 1‖ ^ n =
          ‖(s : ℂ) * Complex.I + 1‖ ^ (l - 2 * j) * ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l - 2 * j)) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      have h1 : ‖(s : ℂ) * Complex.I‖ ^ (l - 2 * j) / ‖(s : ℂ) * Complex.I + 1‖ ^ (l - 2 * j) ≤ 1 :=
        (div_le_one (by positivity)).mpr (pow_le_pow_left₀ (norm_nonneg _) hle_den _)
      have h2 : 1 / ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l - 2 * j)) ≤ (1 + s ^ 2)⁻¹ := by
        rw [one_div]
        calc (‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l - 2 * j)))⁻¹
            ≤ (‖(s : ℂ) * Complex.I + 1‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hge1 (by omega))
          _ = (1 + s ^ 2)⁻¹ := by rw [hnsq]
      calc ‖(s : ℂ) * Complex.I‖ ^ (l - 2 * j) /
            (‖(s : ℂ) * Complex.I + 1‖ ^ (l - 2 * j) * ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l - 2 * j)))
          = (‖(s : ℂ) * Complex.I‖ ^ (l - 2 * j) / ‖(s : ℂ) * Complex.I + 1‖ ^ (l - 2 * j)) *
              (1 / ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l - 2 * j))) := by ring
        _ ≤ 1 * (1 + s ^ 2)⁻¹ := mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = (1 + s ^ 2)⁻¹ := one_mul _
    have hind : ∀ (S : Finset ℕ), S ⊆ Finset.Ico p (p + q) →
        Integrable (fun s : ℝ => ∑ l ∈ S,
          ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l - 2 * j) / ((s : ℂ) * Complex.I + 1) ^ n)) ∧
        ∫ s : ℝ, (∑ l ∈ S,
          ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l - 2 * j) / ((s : ℂ) * Complex.I + 1) ^ n)) = 0 := by
      intro S hS
      induction S using Finset.cons_induction with
      | empty => exact ⟨by simp, by simp⟩
      | cons l S hlS ih =>
        have hl_mem : l ∈ Finset.Ico p (p + q) := hS (Finset.mem_cons_self l S)
        have hS' : S ⊆ Finset.Ico p (p + q) := fun x hx => hS (Finset.mem_cons_of_mem hx)
        have h1 := hterm_int l hl_mem
        have h2 := ih hS'
        have hln : l ≤ n := by have := (Finset.mem_Ico.mp hl_mem).2; omega
        simp_rw [Finset.sum_cons]
        refine ⟨h1.add h2.1, ?_⟩
        rw [integral_add h1 h2.1, h2.2, add_zero, integral_const_mul,
          integral_I_pow_div_add_one_pow (by omega : (l - 2 * j) + 2 ≤ n), mul_zero]
    exact hind (Finset.Ico p (p + q)) subset_rfl
  have hGre_int : Integrable (fun s : ℝ => (G s).re) :=
    Complex.reCLM.integrable_comp hG_int_and_zero.1
  have hGre_even : ∀ s : ℝ, (G (-s)).re = (G s).re := by
    intro s
    by_cases hs : s = 0
    · simp [hs]
    · have h1 := hG_eq s hs
      have h2 := hG_eq (-s) (neg_ne_zero.mpr hs)
      rw [phiPQ_imag_even_re, even_two_mul j |>.neg_pow s] at h2
      have hpow : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
      exact mul_left_cancel₀ hpow (h2.symm.trans h1)
  have hGre_zero : ∫ s : ℝ, (G s).re = 0 := by
    have := Complex.reCLM.integral_comp_comm hG_int_and_zero.1
    change ∫ s : ℝ, (G s).re = (∫ s : ℝ, G s).re at this
    rw [this, hG_int_and_zero.2, Complex.zero_re]
  have hcongr : EqOn (fun s : ℝ => (phiPQ p q 1 ((s : ℂ) * Complex.I)).re / s ^ (2 * j))
      (fun s : ℝ => ((-1 : ℝ) ^ j) * (G s).re) (Ioi 0) :=
    fun s hs => hG_eq s (mem_Ioi.mp hs).ne'
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    setIntegral_Ioi_eq_half_of_even hGre_int hGre_even, hGre_zero, mul_zero, mul_zero]

/-- **Lemma `fct:phikill` (2), second identity**:
`∫_0^∞ t^{2k} (1 - Re(φ_{p,q}(it; a))) dt = 0` for `2k + 2 ≤ q`, `p ≥ 1`, `a > 0`. -/
theorem phiPQ_moment_pos {p q k : ℕ} (hq : 2 * k + 2 ≤ q) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re) = 0 := by
  have hq1 : 1 ≤ q := by omega
  -- Reduce to `a = 1` by scaling `t = a * s`
  have hcov : ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re) =
      a ^ (2 * k + 1) * ∫ s in Ioi (0 : ℝ), s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re) := by
    have h1 := integral_comp_mul_left_Ioi
      (fun t : ℝ => t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re)) (0 : ℝ) ha
    simp only [mul_zero, smul_eq_mul] at h1
    have h2 : ∫ s in Ioi (0 : ℝ), (a * s) ^ (2 * k) * (1 - (phiPQ p q a (((a * s : ℝ) : ℂ) * Complex.I)).re) =
        a ^ (2 * k) * ∫ s in Ioi (0 : ℝ), s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      rw [phiPQ_scale ha]
      have harg : ((a * s : ℝ) : ℂ) * Complex.I / (a : ℂ) = (s : ℂ) * Complex.I := by
        have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
        push_cast; field_simp
      rw [harg, mul_pow]; ring
    rw [h2] at h1
    have ha_ne : a ≠ 0 := ha.ne'
    calc ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re)
        = a * (a⁻¹ * ∫ t in Ioi (0 : ℝ), t ^ (2 * k) * (1 - (phiPQ p q a ((t : ℂ) * Complex.I)).re)) := by
          rw [← mul_assoc, mul_inv_cancel₀ ha_ne, one_mul]
      _ = a * (a ^ (2 * k) * ∫ s in Ioi (0 : ℝ), s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re)) := by
          rw [← h1]
      _ = a ^ (2 * k + 1) * ∫ s in Ioi (0 : ℝ), s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re) := by
          rw [← mul_assoc, ← pow_succ']
  rw [hcov]
  suffices h0 : ∫ s in Ioi (0 : ℝ), s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re) = 0 by
    rw [h0, mul_zero]
  set n : ℕ := p + q - 1
  have hne : ∀ s : ℝ, (s : ℂ) * Complex.I + 1 ≠ 0 := fun s h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Complex.one_re, zero_add,
      Complex.zero_re] at this
    norm_num at this
  let G : ℝ → ℂ := fun s => ∑ l ∈ Finset.range p,
    ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l + 2 * k) / ((s : ℂ) * Complex.I + 1) ^ n)
  have hG_eq : ∀ s : ℝ,
      s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re) = ((-1 : ℝ) ^ k) * (G s).re := by
    intro s
    have hpowI : ((s : ℂ) * Complex.I) ^ (2 * k) = ((((-1 : ℝ) ^ k * s ^ (2 * k) : ℝ)) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]; push_cast; ring
    have hmul : ((s : ℂ) * Complex.I) ^ (2 * k) * (1 - phiPQ p q 1 ((s : ℂ) * Complex.I)) = G s := by
      rw [one_sub_phiPQ hq1 (by simpa using hne s)]
      simp only [Complex.ofReal_one, G, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hlp : l < p := Finset.mem_range.mp hl
      have hln : l + (n - l) = n := by omega
      have hpow_den : ((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l) =
          ((s : ℂ) * Complex.I + 1) ^ n := by rw [← pow_add, hln]
      rw [div_pow, div_pow, one_pow]
      change ((s : ℂ) * Complex.I) ^ (2 * k) * (((Nat.choose n l : ℝ) : ℂ) *
          (((s : ℂ) * Complex.I) ^ l / ((s : ℂ) * Complex.I + 1) ^ l) *
          (1 / ((s : ℂ) * Complex.I + 1) ^ (n - l))) = _
      field_simp [hne s]
      calc ((s : ℂ) * Complex.I) ^ (2 * k) * ((Nat.choose n l : ℝ) : ℂ) * ((s : ℂ) * Complex.I) ^ l *
              ((s : ℂ) * Complex.I + 1) ^ n
          = ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l)) *
              (((s : ℂ) * Complex.I) ^ l * ((s : ℂ) * Complex.I) ^ (2 * k)) := by
              rw [hpow_den]; ring
        _ = ((Nat.choose n l : ℝ) : ℂ) * ((s : ℂ) * Complex.I + 1) ^ l * ((s : ℂ) * Complex.I + 1) ^ (n - l) *
              ((s : ℂ) * Complex.I) ^ (l + 2 * k) := by rw [← pow_add]; ring
    have hre := congrArg Complex.re hmul
    rw [hpowI, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re] at hre
    have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
    calc s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re)
        = (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * s ^ (2 * k) * (1 - (phiPQ p q 1 ((s : ℂ) * Complex.I)).re)) := by
          rw [← mul_assoc, ← mul_assoc, hsq, one_mul]
      _ = (-1 : ℝ) ^ k * (G s).re := by rw [hre]
  have hG_int_and_zero : Integrable G ∧ ∫ s : ℝ, G s = 0 := by
    have hterm_int : ∀ l ∈ Finset.range p,
        Integrable (fun s : ℝ => ((Nat.choose n l : ℝ) : ℂ) *
          (((s : ℂ) * Complex.I) ^ (l + 2 * k) / ((s : ℂ) * Complex.I + 1) ^ n)) := by
      intro l hl
      have hlp : l < p := Finset.mem_range.mp hl
      have hdeg : (l + 2 * k) + 2 ≤ n := by omega
      refine Integrable.const_mul ?_ _
      have hcont : Continuous (fun s : ℝ => ((s : ℂ) * Complex.I) ^ (l + 2 * k) / ((s : ℂ) * Complex.I + 1) ^ n) :=
        ((Complex.continuous_ofReal.mul continuous_const).pow _).div
          (((Complex.continuous_ofReal.mul continuous_const).add continuous_const).pow _)
          fun s => pow_ne_zero _ (hne s)
      refine integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      have hnsq : ‖(s : ℂ) * Complex.I + 1‖ ^ 2 = 1 + s ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      have hge1 : 1 ≤ ‖(s : ℂ) * Complex.I + 1‖ :=
        le_of_sq_le_sq (by rw [hnsq]; nlinarith [sq_nonneg s]) (norm_nonneg _)
      have hle_den : ‖(s : ℂ) * Complex.I‖ ≤ ‖(s : ℂ) * Complex.I + 1‖ := by
        have h1 : ‖(s : ℂ) * Complex.I‖ ^ 2 = s ^ 2 := by rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, sq_abs]
        exact le_of_sq_le_sq (by rw [h1, hnsq]; linarith) (norm_nonneg _)
      rw [norm_div, norm_pow, norm_pow]
      have hsplit : ‖(s : ℂ) * Complex.I + 1‖ ^ n =
          ‖(s : ℂ) * Complex.I + 1‖ ^ (l + 2 * k) * ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l + 2 * k)) := by
        rw [← pow_add]; congr 1; omega
      rw [hsplit]
      have h1 : ‖(s : ℂ) * Complex.I‖ ^ (l + 2 * k) / ‖(s : ℂ) * Complex.I + 1‖ ^ (l + 2 * k) ≤ 1 :=
        (div_le_one (by positivity)).mpr (pow_le_pow_left₀ (norm_nonneg _) hle_den _)
      have h2 : 1 / ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l + 2 * k)) ≤ (1 + s ^ 2)⁻¹ := by
        rw [one_div]
        calc (‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l + 2 * k)))⁻¹
            ≤ (‖(s : ℂ) * Complex.I + 1‖ ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hge1 (by omega))
          _ = (1 + s ^ 2)⁻¹ := by rw [hnsq]
      calc ‖(s : ℂ) * Complex.I‖ ^ (l + 2 * k) /
            (‖(s : ℂ) * Complex.I + 1‖ ^ (l + 2 * k) * ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l + 2 * k)))
          = (‖(s : ℂ) * Complex.I‖ ^ (l + 2 * k) / ‖(s : ℂ) * Complex.I + 1‖ ^ (l + 2 * k)) *
              (1 / ‖(s : ℂ) * Complex.I + 1‖ ^ (n - (l + 2 * k))) := by ring
        _ ≤ 1 * (1 + s ^ 2)⁻¹ := mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = (1 + s ^ 2)⁻¹ := one_mul _
    have hind : ∀ (S : Finset ℕ), S ⊆ Finset.range p →
        Integrable (fun s : ℝ => ∑ l ∈ S,
          ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l + 2 * k) / ((s : ℂ) * Complex.I + 1) ^ n)) ∧
        ∫ s : ℝ, (∑ l ∈ S,
          ((Nat.choose n l : ℝ) : ℂ) * (((s : ℂ) * Complex.I) ^ (l + 2 * k) / ((s : ℂ) * Complex.I + 1) ^ n)) = 0 := by
      intro S hS
      induction S using Finset.cons_induction with
      | empty => exact ⟨by simp, by simp⟩
      | cons l S hlS ih =>
        have hl_mem : l ∈ Finset.range p := hS (Finset.mem_cons_self l S)
        have hS' : S ⊆ Finset.range p := fun x hx => hS (Finset.mem_cons_of_mem hx)
        have h1 := hterm_int l hl_mem
        have h2 := ih hS'
        have hlp : l < p := Finset.mem_range.mp hl_mem
        simp_rw [Finset.sum_cons]
        refine ⟨h1.add h2.1, ?_⟩
        rw [integral_add h1 h2.1, h2.2, add_zero, integral_const_mul,
          integral_I_pow_div_add_one_pow (by omega : (l + 2 * k) + 2 ≤ n), mul_zero]
    exact hind (Finset.range p) subset_rfl
  have hGre_int : Integrable (fun s : ℝ => (G s).re) :=
    Complex.reCLM.integrable_comp hG_int_and_zero.1
  have hGre_even : ∀ s : ℝ, (G (-s)).re = (G s).re := by
    intro s
    have h1 := hG_eq s
    have h2 := hG_eq (-s)
    rw [phiPQ_imag_even_re, even_two_mul k |>.neg_pow s] at h2
    have hpow : (-1 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    exact mul_left_cancel₀ hpow (h2.symm.trans h1)
  have hGre_zero : ∫ s : ℝ, (G s).re = 0 := by
    have := Complex.reCLM.integral_comp_comm hG_int_and_zero.1
    change ∫ s : ℝ, (G s).re = (∫ s : ℝ, G s).re at this
    rw [this, hG_int_and_zero.2, Complex.zero_re]
  simp_rw [hG_eq]
  rw [integral_const_mul, setIntegral_Ioi_eq_half_of_even hGre_int hGre_even, hGre_zero, mul_zero, mul_zero]

end FormalResearch.SignUncertainty.FctPhiKill
