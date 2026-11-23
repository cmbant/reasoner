module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryDef
public import FormalResearch.ModularBootstrap.Upper.Holes.Peano
public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauDeriv

/-!
# Midpoint comparison on the quantile cells (`rem:P1.2`(2), Step 2 (S))

For a `C²` function `G` on `(0, ∞)` with `|G'(y)| ≤ A/(1+y)`, `|G''(y)| ≤ A/(1+y)²` on `[ξ_*, ∞)`:

* `cell_midpoint`: `|G(χ_k) - ∫_{k-1/2}^{k+1/2} G(χ_a) da| ≤ M/24` when `|(G∘χ)''| ≤ M` on the cell;
* `midpoint_sum_le`: `∑_{k = 2}^n |G(χ_k) - ∫_{cell k} G(χ_a) da| ≤ C A λ` (tip cells by `(F1)`,
  `|(G∘χ)''| ≤ A χ'^2 (1 + (log ρ_U)') ≤ C A λ a^{-4/3}`; far cells by `|(G∘χ)''| ≤ C A (a - 1/4)^{-2}`,
  summed from `k ≳ c'`);
* `midpoint_head_le`: `|G(χ_1) - 2∫_{1/4}^{3/2} G(χ_a) da + (3/2) G(ξ_*)| ≤ C A λ`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes

lemma continuousAt_rhoUDeriv {y : ℝ} (hy : xiStar < y) : ContinuousAt rhoUDeriv y := by
  have h1 : 0 < Real.sinh (π * y) ^ 2 - 1 := by
    have h2 : 1 < Real.sinh (π * y) := by
      rw [← sinh_pi_mul_xiStar]
      exact Real.sinh_lt_sinh.2 (by have := Real.pi_pos; nlinarith)
    nlinarith
  unfold rhoUDeriv
  refine continuousAt_const.mul (ContinuousAt.div ?_ ?_ ?_)
  · exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousAt
  · exact ContinuousAt.sqrt (((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2).sub
      continuous_const).continuousAt
  · exact (Real.sqrt_pos.2 h1).ne'

lemma continuousOn_chiSecond {c' : ℝ} (hc' : 0 < c') : ContinuousOn (chiSecond c') (Ioi (1 / 4)) := by
  intro a ha
  have ha' : 1 / 4 < a := ha
  have hχ := xiStar_lt_chiQuantile hc' ha'
  have hcd : ContinuousAt (chiDeriv c') a := (hasDerivAt_chiQuantile hc' ha').2.continuousAt
  have hχc : ContinuousAt (chiQuantile c') a := continuousAt_chiQuantile hc' ha'
  have hρ : ContinuousAt rhoU (chiQuantile c' a) :=
    (continuousOn_rhoU.continuousAt (Ici_mem_nhds hχ))
  have hρ' : ContinuousAt rhoUDeriv (chiQuantile c' a) := continuousAt_rhoUDeriv hχ
  have hne : rhoU (chiQuantile c' a) ≠ 0 := (rhoU_pos hχ).ne'
  unfold chiSecond
  refine ContinuousAt.continuousWithinAt ?_
  exact (hcd.pow 2).neg.mul ((hρ'.comp hχc).div (hρ.comp hχc) hne)

/-- `G ∘ χ` has the second derivative `G''(χ) χ'^2 + G'(χ) χ''`. -/
lemma hasDerivAt_comp_chi {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ}
    (hG1 : ∀ y : ℝ, 0 < y → HasDerivAt G (deriv G y) y)
    (hG2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv G) (deriv (deriv G) y) y) {a : ℝ} (ha : 1 / 4 < a) :
    HasDerivAt (fun t => G (chiQuantile c' t)) (deriv G (chiQuantile c' a) * chiDeriv c' a) a ∧
    HasDerivAt (fun t => deriv G (chiQuantile c' t) * chiDeriv c' t)
      (deriv (deriv G) (chiQuantile c' a) * chiDeriv c' a ^ 2 +
        deriv G (chiQuantile c' a) * chiSecond c' a) a := by
  have hχ := xiStar_lt_chiQuantile hc' ha
  have hy : 0 < chiQuantile c' a := lt_trans xiStar_pos hχ
  obtain ⟨hd1, hd2⟩ := hasDerivAt_chiQuantile hc' ha
  refine ⟨(hG1 _ hy).comp a hd1, ?_⟩
  have := ((hG2 _ hy).comp a hd1).mul hd2
  refine this.congr_deriv ?_
  simp only [Function.comp]
  ring

/-- Midpoint comparison on one cell. -/
lemma cell_midpoint {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ}
    (hG1 : ∀ y : ℝ, 0 < y → HasDerivAt G (deriv G y) y)
    (hG2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv G) (deriv (deriv G) y) y)
    (hGc : ContinuousOn (deriv (deriv G)) (Ioi 0)) {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hM : ∀ t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      |deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
        deriv G (chiQuantile c' t) * chiSecond c' t| ≤ M) :
    |G (chiQuantile c' (k : ℝ)) - ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), G (chiQuantile c' t)| ≤
      M / 24 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcell : ∀ t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), 1 / 4 < t := fun t ht => by
    linarith [ht.1]
  have hder := fun t (ht : t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) =>
    hasDerivAt_comp_chi hc' hG1 hG2 (hcell t ht)
  have hcont : ContinuousOn (fun t => deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
      deriv G (chiQuantile c' t) * chiSecond c' t) (Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) := by
    have hχc : ContinuousOn (chiQuantile c') (Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      fun t ht => (continuousAt_chiQuantile hc' (hcell t ht)).continuousWithinAt
    have hχpos : MapsTo (chiQuantile c') (Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) (Ioi 0) :=
      fun t ht => lt_trans xiStar_pos (xiStar_lt_chiQuantile hc' (hcell t ht))
    have hcd : ContinuousOn (chiDeriv c') (Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      fun t ht => ((hasDerivAt_chiQuantile hc' (hcell t ht)).2.continuousAt).continuousWithinAt
    have hcs : ContinuousOn (chiSecond c') (Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      (continuousOn_chiSecond hc').mono fun t ht => hcell t ht
    have hG1c : ContinuousOn (deriv G) (Ioi 0) := fun y hy =>
      (hG2 y hy).continuousAt.continuousWithinAt
    exact ((hGc.comp hχc hχpos).mul (hcd.pow 2)).add ((hG1c.comp hχc hχpos).mul hcs)
  have hle := midpoint_peano_ge (g := fun t => G (chiQuantile c' t))
    (g' := fun t => deriv G (chiQuantile c' t) * chiDeriv c' t)
    (g'' := fun t => deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
        deriv G (chiQuantile c' t) * chiSecond c' t) (k := (k : ℝ)) (M := M)
    (fun t ht => (hder t ht).1) (fun t ht => (hder t ht).2) hcont
    (fun t ht => (le_abs_self _).trans (hM t ht))
  have hge := midpoint_peano_le (g := fun t => G (chiQuantile c' t))
    (g' := fun t => deriv G (chiQuantile c' t) * chiDeriv c' t)
    (g'' := fun t => deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
        deriv G (chiQuantile c' t) * chiSecond c' t) (k := (k : ℝ)) (M := M)
    (fun t ht => (hder t ht).1) (fun t ht => (hder t ht).2) hcont
    (fun t ht => (neg_le_abs _).trans (hM t ht))
  rw [abs_le]
  constructor <;> linarith

/-- `|(G∘χ)''|` at `a`. -/
noncomputable def gpp (c' : ℝ) (G : ℝ → ℝ) (a : ℝ) : ℝ :=
  |deriv (deriv G) (chiQuantile c' a) * chiDeriv c' a ^ 2 + deriv G (chiQuantile c' a) * chiSecond c' a|

/-- The quantile-cell second derivative in terms of `χ'^2 (1/(1+y)^2 + (ρ'/ρ)/(1+y))`. -/
lemma gpp_le_basic {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ} {A : ℝ} {a : ℝ} (ha : 1 / 4 < a)
    (hG1 : |deriv G (chiQuantile c' a)| ≤ A / (1 + chiQuantile c' a))
    (hG2 : |deriv (deriv G) (chiQuantile c' a)| ≤ A / (1 + chiQuantile c' a) ^ 2) :
    gpp c' G a ≤ A * (chiDeriv c' a ^ 2 * (1 / (1 + chiQuantile c' a) ^ 2 +
      (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) / (1 + chiQuantile c' a))) := by
  have hχ := xiStar_lt_chiQuantile hc' ha
  have hy : 0 < 1 + chiQuantile c' a := by linarith [xiStar_pos]
  have hq : 0 ≤ rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a) := by
    have := rhoUDeriv_ge hχ
    have h2 := rhoU_pos hχ
    positivity
  unfold gpp chiSecond
  set y := chiQuantile c' a
  set q := rhoUDeriv y / rhoU y
  set d := chiDeriv c' a
  have h1 : |deriv (deriv G) y * d ^ 2 + deriv G y * (-d ^ 2 * q)| ≤
      |deriv (deriv G) y| * d ^ 2 + |deriv G y| * (d ^ 2 * q) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg d)]
    have : |(-d ^ 2 * q)| = d ^ 2 * q := by
      rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg d), abs_of_nonneg hq]
    rw [this]
  refine h1.trans ?_
  have e1 : |deriv (deriv G) y| * d ^ 2 ≤ A / (1 + y) ^ 2 * d ^ 2 := by gcongr
  have e2 : |deriv G y| * (d ^ 2 * q) ≤ A / (1 + y) * (d ^ 2 * q) := by
    have : 0 ≤ d ^ 2 * q := by positivity
    gcongr
  calc _ ≤ A / (1 + y) ^ 2 * d ^ 2 + A / (1 + y) * (d ^ 2 * q) := add_le_add e1 e2
    _ = A * (d ^ 2 * (1 / (1 + y) ^ 2 + q / (1 + y))) := by field_simp

/-- Tip cells: `|(G∘χ)''(a)| ≤ C_T A λ a^{-4/3}` for `a ≥ 1`, `χ_a - ξ_* ≤ 0.63`. -/
theorem gpp_tip :
    ∃ CT : ℝ, 0 < CT ∧ ∀ {c' : ℝ}, 0 < c' → ∀ {G : ℝ → ℝ} {A : ℝ}, 0 ≤ A →
      ∀ {a : ℝ}, 1 ≤ a → siteRadius c' a ≤ 63 / 100 →
      (∀ y : ℝ, xiStar ≤ y → |deriv G y| ≤ A / (1 + y)) →
      (∀ y : ℝ, xiStar ≤ y → |deriv (deriv G) y| ≤ A / (1 + y) ^ 2) →
      gpp c' G a ≤ A * CT * lambdaComb c' * a ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨CT, hCT, h⟩ := chiDeriv_sq_logDeriv_le
  refine ⟨CT, hCT, fun {c'} hc' {G} {A} hA {a} ha hr hG1 hG2 => ?_⟩
  have ha4 : 1 / 4 < a := by linarith
  have hχ := xiStar_lt_chiQuantile hc' ha4
  have hy : 1 ≤ 1 + chiQuantile c' a := by linarith [xiStar_pos]
  have hq : 0 ≤ rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a) := by
    have := rhoUDeriv_ge hχ
    have h2 := rhoU_pos hχ
    positivity
  refine (gpp_le_basic hc' ha4 (hG1 _ hχ.le) (hG2 _ hχ.le)).trans ?_
  have hb := h c' hc' a ha hr
  have e1 : 1 / (1 + chiQuantile c' a) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have e2 : (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) / (1 + chiQuantile c' a) ≤
      rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a) := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have e3 : chiDeriv c' a ^ 2 * (1 / (1 + chiQuantile c' a) ^ 2 +
      (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) / (1 + chiQuantile c' a)) ≤
      chiDeriv c' a ^ 2 * (1 + rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) := by
    gcongr
  calc _ ≤ A * (chiDeriv c' a ^ 2 * (1 + rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))) := by
        gcongr
    _ ≤ A * (CT * lambdaComb c' * a ^ (-(4 / 3 : ℝ))) := by gcongr
    _ = _ := by ring

/-- Cumulative count growth: for `χ_a ≥ ξ_* + 1/2`, `a - 1/4 ≤ K₁ c' (χ_a - ξ_*)²`. -/
theorem far_growth :
    ∃ K1 : ℝ, 0 < K1 ∧ ∀ {c' : ℝ}, 0 < c' → ∀ {a : ℝ}, 1 / 4 ≤ a →
      xiStar + 1 / 2 ≤ chiQuantile c' a → a - 1 / 4 ≤ K1 * c' * (chiQuantile c' a - xiStar) ^ 2 := by
  have hk := kTip_pos
  set B : ℝ := 3 * kTip / 2 + 4 / 3
  refine ⟨3 * B / 2, by positivity, fun {c'} hc' {a} ha hr => ?_⟩
  set r := chiQuantile c' a - xiStar with hrdef
  have hr0 : 1 / 2 ≤ r := by linarith
  have hspec := (chiQuantile_spec hc' ha).2
  have hN := cumulN_le_half_mul (x := chiQuantile c' a) (chiQuantile_spec hc' ha).1
  have hρ : rhoU (xiStar + r) ≤ B * (1 + r) := rhoU_le_linear (r := r) (by linarith)
  have hxr : xiStar + r = chiQuantile c' a := by rw [hrdef]; ring
  rw [hxr] at hρ
  have hρ0 := rhoU_nonneg (chiQuantile c' a)
  have : cumulN (chiQuantile c' a) ≤ r * (B * (1 + r)) / 2 := by
    refine hN.trans ?_
    rw [← hrdef]
    have := mul_le_mul_of_nonneg_left hρ (by linarith : 0 ≤ r)
    linarith
  have h2 : r * (B * (1 + r)) / 2 ≤ 3 * B / 2 * r ^ 2 := by
    have hB : 0 < B := by positivity
    nlinarith [mul_nonneg (mul_nonneg hB.le (by linarith : 0 ≤ r)) (by linarith : 0 ≤ 2 * r - 1)]
  have := mul_le_mul_of_nonneg_left (this.trans h2) hc'.le
  nlinarith

/-- Far cells: `|(G∘χ)''(a)| ≤ C_F A (a - 1/4)^{-2}` for `χ_a ≥ ξ_* + 1/2`. -/
theorem gpp_far :
    ∃ CF : ℝ, 0 < CF ∧ ∀ {c' : ℝ}, 0 < c' → ∀ {G : ℝ → ℝ} {A : ℝ}, 0 ≤ A →
      ∀ {a : ℝ}, 1 / 4 < a → xiStar + 1 / 2 ≤ chiQuantile c' a →
      (∀ y : ℝ, xiStar ≤ y → |deriv G y| ≤ A / (1 + y)) →
      (∀ y : ℝ, xiStar ≤ y → |deriv (deriv G) y| ≤ A / (1 + y) ^ 2) →
      gpp c' G a ≤ A * CF / (a - 1 / 4) ^ 2 := by
  obtain ⟨Cd, hCd, hd⟩ := chiDeriv_large_le (r1 := 1 / 2) (by norm_num)
  obtain ⟨Cl, hCl, hl⟩ := logDeriv_rhoU_large_le (r1 := 1 / 2) (by norm_num)
  obtain ⟨K1, hK1, hK⟩ := far_growth
  refine ⟨Cd ^ 2 * (1 + Cl) * K1 ^ 2, by positivity, fun {c'} hc' {G} {A} hA {a} ha hr hG1 hG2 => ?_⟩
  have hχ := xiStar_lt_chiQuantile hc' ha
  set y := chiQuantile c' a with hy
  have hxs := xiStar_pos
  have hy1 : 0 < 1 + y := by linarith
  have hq0 : 0 ≤ rhoUDeriv y / rhoU y := by
    have := rhoUDeriv_ge hχ
    have h2 := rhoU_pos hχ
    positivity
  refine (gpp_le_basic hc' ha (hG1 _ hχ.le) (hG2 _ hχ.le)).trans ?_
  have hd' := hd c' hc' a hr
  have hl' := hl y hr
  have hcd0 : 0 ≤ chiDeriv c' a := by
    unfold chiDeriv; have := rhoU_pos hχ; positivity
  have h1 : chiDeriv c' a ^ 2 ≤ (Cd / (c' * (1 + y))) ^ 2 := by gcongr
  have hgrow := hK hc' ha.le hr
  have hra : 1 / 2 ≤ y - xiStar := by linarith
  have ha0 : 0 < a - 1 / 4 := by linarith
  have hr2 : (a - 1 / 4) ≤ K1 * c' * (1 + y) ^ 2 := by
    refine hgrow.trans ?_
    have : (y - xiStar) ^ 2 ≤ (1 + y) ^ 2 := by
      apply pow_le_pow_left₀ (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  -- A * (χ'² (1/(1+y)² + q/(1+y))) ≤ A * Cd²(1+Cl)/(c'² (1+y)⁴)
  have h3 : chiDeriv c' a ^ 2 * (1 / (1 + y) ^ 2 + (rhoUDeriv y / rhoU y) / (1 + y)) ≤
      (Cd / (c' * (1 + y))) ^ 2 * ((1 + Cl) / (1 + y) ^ 2) := by
    have : 1 / (1 + y) ^ 2 + (rhoUDeriv y / rhoU y) / (1 + y) ≤ (1 + Cl) / (1 + y) ^ 2 := by
      have : (rhoUDeriv y / rhoU y) / (1 + y) ≤ Cl / (1 + y) ^ 2 := by
        rw [div_le_div_iff₀ hy1 (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hl' hy1.le, div_mul_cancel₀ Cl hy1.ne']
      calc _ ≤ 1 / (1 + y) ^ 2 + Cl / (1 + y) ^ 2 := by linarith
        _ = _ := by ring
    exact mul_le_mul h1 this (by positivity) (by positivity)
  have h4 : (Cd / (c' * (1 + y))) ^ 2 * ((1 + Cl) / (1 + y) ^ 2) ≤
      Cd ^ 2 * (1 + Cl) * K1 ^ 2 / (a - 1 / 4) ^ 2 := by
    have e : (Cd / (c' * (1 + y))) ^ 2 * ((1 + Cl) / (1 + y) ^ 2) =
        Cd ^ 2 * (1 + Cl) / (c' ^ 2 * ((1 + y) ^ 2) ^ 2) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h5 : (a - 1 / 4) ^ 2 ≤ (K1 * c' * (1 + y) ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ ha0.le hr2
    have hnn : 0 ≤ Cd ^ 2 * (1 + Cl) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h5 hnn]
  calc A * (chiDeriv c' a ^ 2 * (1 / (1 + y) ^ 2 + (rhoUDeriv y / rhoU y) / (1 + y)))
      ≤ A * (Cd ^ 2 * (1 + Cl) * K1 ^ 2 / (a - 1 / 4) ^ 2) := by gcongr; exact h3.trans h4
    _ = _ := by ring

/-- A smooth kernel `G` with `|G'(y)| ≤ A/(1+y)`, `|G''(y)| ≤ A/(1+y)²` on `[ξ_*, ∞)`. -/
structure KernelHyp (G : ℝ → ℝ) (A : ℝ) : Prop where
  nonneg : 0 ≤ A
  d1 : ∀ y : ℝ, 0 < y → HasDerivAt G (deriv G y) y
  d2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv G) (deriv (deriv G) y) y
  c2 : ContinuousOn (deriv (deriv G)) (Ioi 0)
  b1 : ∀ y : ℝ, xiStar ≤ y → |deriv G y| ≤ A / (1 + y)
  b2 : ∀ y : ℝ, xiStar ≤ y → |deriv (deriv G) y| ≤ A / (1 + y) ^ 2

/-- Tail of `∑ (k - 3/4)^{-2}`. -/
lemma sum_inv_sq_tail {B : ℝ} (hB : 2 ≤ B) (n : ℕ) :
    ∑ k ∈ (Finset.Icc 2 n).filter (fun k : ℕ => B ≤ (k : ℝ)), ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) ≤
      2 / (B - 1) := by
  set m := ⌈B⌉₊ with hm
  have hmB : B ≤ m := Nat.le_ceil B
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ m := hB.trans hmB
    exact_mod_cast this
  have hterm : ∀ k ∈ (Finset.Icc 2 n).filter (fun k : ℕ => B ≤ (k : ℝ)),
      ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) ≤ (((k - 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hk1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
      have : 1 ≤ k - 1 := by omega
      exact_mod_cast this
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hcast]
    apply inv_anti₀ (by nlinarith)
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  calc _ ≤ ∑ k ∈ (Finset.Icc 2 n).filter (fun k : ℕ => B ≤ (k : ℝ)), (((k - 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = ∑ i ∈ ((Finset.Icc 2 n).filter (fun k : ℕ => B ≤ (k : ℝ))).image (fun k : ℕ => k - 1),
          (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        have ha2 : 2 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
        have hb2 : 2 ≤ b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
        simp only at hab
        omega
    _ ≤ ∑ i ∈ Finset.Ioo (m - 2) n, (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun (i : ℕ) _ _ => by positivity)
        intro i hi
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hi
        obtain ⟨k, ⟨⟨hk2, hkn⟩, hkB⟩, rfl⟩ := hi
        have : m ≤ k := by
          rw [hm]; exact Nat.ceil_le.mpr hkB
        simp only [Finset.mem_Ioo]
        omega
    _ ≤ 2 / (((m - 2 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ ≤ 2 / (B - 1) := by
        have hc : ((m - 2 : ℕ) : ℝ) + 1 = (m : ℝ) - 1 := by
          rw [Nat.cast_sub hm2]; push_cast; ring
        rw [hc]
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

lemma kern_eq_rpow {k : ℕ} (hk : 1 ≤ k) : kern k = (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  unfold kern cr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.rpow_neg_one, ← Real.rpow_add hk0]; norm_num

lemma inv_le_kTip_lambda {c' : ℝ} (hc' : 1 ≤ c') : 1 / c' ≤ kTip ^ (2 / 3 : ℝ) * lambdaComb c' := by
  have hk := kTip_pos
  have hc0 : 0 < c' := by linarith
  unfold lambdaComb
  rw [Real.mul_rpow hk.le hc0.le, Real.rpow_neg hk.le, Real.rpow_neg hc0.le]
  have h1 : (0 : ℝ) < kTip ^ (2 / 3 : ℝ) := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ h1.ne', one_mul]
  rw [one_div, ← Real.rpow_neg_one]
  rw [← Real.rpow_neg hc0.le]
  exact Real.rpow_le_rpow_of_exponent_le hc' (by norm_num)

/-- One cell: the bound of the second derivative, tip or far. -/
theorem cell_bound :
    ∃ CT CF n0 c0 : ℝ, 0 < CT ∧ 0 < CF ∧ 0 < n0 ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {G : ℝ → ℝ} {A : ℝ},
      KernelHyp G A → ∀ {k : ℕ}, 2 ≤ k →
      |G (chiQuantile c' (k : ℝ)) - ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), G (chiQuantile c' t)| ≤
        A / 24 * ((if siteRadius c' ((k : ℝ) + 1 / 2) ≤ 63 / 100 then
            CT * ((3 / 4 : ℝ) ^ (-(4 / 3 : ℝ))) * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) else 0) +
          (if 63 / 100 < siteRadius c' ((k : ℝ) + 1 / 2) then CF * ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) else 0)) ∧
      (63 / 100 < siteRadius c' ((k : ℝ) + 1 / 2) → c' * n0 - 1 / 4 ≤ (k : ℝ)) := by
  obtain ⟨CT, hCT, hT⟩ := gpp_tip
  obtain ⟨CF, hCF, hF⟩ := gpp_far
  obtain ⟨Cg, hCg, hgap⟩ := siteGap_le_unif
  obtain ⟨c1, hc1⟩ := eventually_atTop.mp hgap
  have hlam0 : ∀ᶠ c' in atTop, 2 * Cg * lambdaComb c' ≤ 13 / 100 := by
    have ht := tendsto_lambdaComb_atTop.const_mul (2 * Cg)
    simp only [mul_zero] at ht
    exact ht.eventually_le_const (by norm_num)
  obtain ⟨c2, hc2⟩ := eventually_atTop.mp hlam0
  set n0 : ℝ := kTip * (63 / 100 : ℝ) ^ (3 / 2 : ℝ) with hn0
  have hn0pos : 0 < n0 := by have := kTip_pos; positivity
  refine ⟨CT, CF, n0, max (max c1 c2) 1, hCT, hCF, hn0pos, by positivity, ?_⟩
  intro c' hc'0 G A hG k hk
  have hc'1 : 1 ≤ c' := (le_max_right _ _).trans hc'0
  have hc' : 0 < c' := by linarith
  have hcc1 : c1 ≤ c' := ((le_max_left _ _).trans (le_max_left _ _)).trans hc'0
  have hcc2 : c2 ≤ c' := ((le_max_right _ _).trans (le_max_left _ _)).trans hc'0
  have hg := hc1 c' hcc1
  have hlam := hc2 c' hcc2
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  -- the F-regime lower bound on `k`
  have hFk : 63 / 100 < siteRadius c' ((k : ℝ) + 1 / 2) → c' * n0 - 1 / 4 ≤ (k : ℝ) := by
    intro hr
    have hspec := (chiQuantile_spec hc' (by linarith : (1 / 4 : ℝ) ≤ (k : ℝ) + 1 / 2)).2
    have hr0 : 0 ≤ siteRadius c' ((k : ℝ) + 1 / 2) := by linarith
    have hb := (cumulN_bounds hr0).1
    have hxr : xiStar + siteRadius c' ((k : ℝ) + 1 / 2) = chiQuantile c' ((k : ℝ) + 1 / 2) := by
      unfold siteRadius; ring
    rw [hxr] at hb
    have h1 : (63 / 100 : ℝ) ^ (3 / 2 : ℝ) ≤ siteRadius c' ((k : ℝ) + 1 / 2) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hr.le (by norm_num)
    have h2 : n0 ≤ cumulN (chiQuantile c' ((k : ℝ) + 1 / 2)) := by
      refine le_trans ?_ hb
      rw [hn0]; exact mul_le_mul_of_nonneg_left h1 kTip_pos.le
    have := mul_le_mul_of_nonneg_left h2 hc'.le
    linarith
  refine ⟨?_, hFk⟩
  -- the bound on `|(G∘χ)''|`
  have hcell : ∀ t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), 1 / 4 < t := fun t ht => by
    linarith [ht.1]
  by_cases hr : siteRadius c' ((k : ℝ) + 1 / 2) ≤ 63 / 100
  · have hM : ∀ t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
        |deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
          deriv G (chiQuantile c' t) * chiSecond c' t| ≤
        A * (CT * ((3 / 4 : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ))) * lambdaComb c') := by
      intro t ht
      have ht1 : 1 ≤ t := by linarith [ht.1]
      have htr : siteRadius c' t ≤ 63 / 100 := by
        refine le_trans ?_ hr
        unfold siteRadius
        have := chiQuantile_mono_le hc' (by linarith : (1 / 4 : ℝ) ≤ t) ht.2
        linarith
      have h := hT hc' hG.nonneg ht1 htr hG.b1 hG.b2
      have hkk : ((3 / 4 : ℝ) * k) ≤ t := by linarith [ht.1]
      have hpow : t ^ (-(4 / 3 : ℝ)) ≤ ((3 / 4 : ℝ) * k) ^ (-(4 / 3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hkk (by norm_num)
      rw [Real.mul_rpow (by norm_num) (by linarith)] at hpow
      unfold gpp at h
      refine h.trans ?_
      have hA := hG.nonneg
      have := (lamPos hc').le
      calc A * CT * lambdaComb c' * t ^ (-(4 / 3 : ℝ))
          ≤ A * CT * lambdaComb c' * ((3 / 4 : ℝ) ^ (-(4 / 3 : ℝ)) * (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
            gcongr
        _ = _ := by ring
    have := cell_midpoint hc' hG.d1 hG.d2 hG.c2 (by omega : 1 ≤ k) hM
    simp only [hr, ite_true, not_lt.mpr hr, ite_false, add_zero]
    refine this.trans (le_of_eq ?_)
    ring
  · have hr' : 63 / 100 < siteRadius c' ((k : ℝ) + 1 / 2) := lt_of_not_ge hr
    have hM : ∀ t ∈ Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
        |deriv (deriv G) (chiQuantile c' t) * chiDeriv c' t ^ 2 +
          deriv G (chiQuantile c' t) * chiSecond c' t| ≤ A * (CF * ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ))) := by
      intro t ht
      have ht4 := hcell t ht
      -- cell length
      have hlen : chiQuantile c' ((k : ℝ) + 1 / 2) - chiQuantile c' ((k : ℝ) - 1 / 2) ≤ 2 * Cg * lambdaComb c' := by
        have h1 : chiQuantile c' ((k : ℝ) + 1 / 2) ≤ chiQuantile c' ((k : ℝ) + 1) :=
          chiQuantile_mono_le hc' (by linarith) (by linarith)
        have h2 : chiQuantile c' ((k : ℝ) - 1) ≤ chiQuantile c' ((k : ℝ) - 1 / 2) :=
          chiQuantile_mono_le hc' (by linarith) (by linarith)
        have hk1' : 1 ≤ k - 1 := by omega
        have g1 := (hg (k - 1) hk1').1
        have g2 := (hg k (by omega)).1
        have e1 : siteGap c' (k - 1 : ℕ) = chiQuantile c' (k : ℝ) - chiQuantile c' ((k : ℝ) - 1) := by
          unfold siteGap
          rw [Nat.cast_sub (by omega)]
          norm_num
        have e2 : siteGap c' k = chiQuantile c' ((k : ℝ) + 1) - chiQuantile c' (k : ℝ) := rfl
        linarith
      have hχt : xiStar + 1 / 2 ≤ chiQuantile c' t := by
        have h3 : chiQuantile c' ((k : ℝ) - 1 / 2) ≤ chiQuantile c' t :=
          chiQuantile_mono_le hc' (by linarith) ht.1
        unfold siteRadius at hr'
        linarith
      have h := hF hc' hG.nonneg ht4 hχt hG.b1 hG.b2
      unfold gpp at h
      refine h.trans ?_
      have hA := hG.nonneg
      have hpos : 0 < t - 1 / 4 := by linarith
      have hle : (k : ℝ) - 3 / 4 ≤ t - 1 / 4 := by linarith [ht.1]
      have hkp : 0 < (k : ℝ) - 3 / 4 := by linarith
      have h5 : A * CF / (t - 1 / 4) ^ 2 ≤ A * CF / ((k : ℝ) - 3 / 4) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hkp.le hle 2)
      have h6 : A * (CF * ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ))) = A * CF / ((k : ℝ) - 3 / 4) ^ 2 := by
        rw [Real.rpow_neg hkp.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [h6]; exact h5
    have := cell_midpoint hc' hG.d1 hG.d2 hG.c2 (by omega : 1 ≤ k) hM
    simp only [hr, ite_false, hr', ite_true, zero_add]
    refine this.trans (le_of_eq ?_)
    ring

/-- **Midpoint sum** (`rem:P1.2`(2), Step 2 (S)): `∑_{k = 2}^n |G(χ_k) - ∫_{cell k} G(χ_a) da| ≤ C A λ`. -/
theorem midpoint_sum_le :
    ∃ C c0 : ℝ, 0 < C ∧ 0 < c0 ∧ ∀ {c' : ℝ}, c0 ≤ c' → ∀ {G : ℝ → ℝ} {A : ℝ}, KernelHyp G A →
      ∀ n : ℕ, ∑ k ∈ Finset.Icc 2 n,
        |G (chiQuantile c' (k : ℝ)) - ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), G (chiQuantile c' t)| ≤
          C * A * lambdaComb c' := by
  obtain ⟨CT, CF, n0, c0', hCT, hCF, hn0, hc0', hcell⟩ := cell_bound
  have hk := kTip_pos
  set c34 : ℝ := (3 / 4 : ℝ) ^ (-(4 / 3 : ℝ)) with hc34
  have hc34p : 0 < c34 := by positivity
  set κ23 : ℝ := kTip ^ (2 / 3 : ℝ) with hκ23
  have hκp : 0 < κ23 := by positivity
  refine ⟨(CT * c34 * kernZ + 4 * CF * κ23 / n0) / 24 + 1, max (max c0' (5 / (2 * n0))) 1, by
    have := kernZ_nonneg; positivity, by positivity, ?_⟩
  intro c' hc'0 G A hG n
  have hc'1 : c0' ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc'0)
  have hc'2 : 5 / (2 * n0) ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc'0)
  have hc'one : 1 ≤ c' := (le_max_right _ _).trans hc'0
  have hc'pos : 0 < c' := by linarith
  have hA := hG.nonneg
  have hlam := lamPos hc'pos
  set B : ℝ := c' * n0 - 1 / 4 with hB
  have hBn : 5 / 2 ≤ c' * n0 := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * n0)).mp hc'2
    linarith
  have hB2 : 2 ≤ B := by rw [hB]; linarith
  have hB1 : c' * n0 / 2 ≤ B - 1 := by rw [hB]; linarith
  have hpt : ∀ k ∈ Finset.Icc 2 n,
      |G (chiQuantile c' (k : ℝ)) - ∫ t in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), G (chiQuantile c' t)| ≤
        A / 24 * ((if siteRadius c' ((k : ℝ) + 1 / 2) ≤ 63 / 100 then
            CT * c34 * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) else 0) +
          (if B ≤ (k : ℝ) then CF * ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) else 0)) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    obtain ⟨h1, h2⟩ := hcell hc'1 hG hk2
    refine h1.trans ?_
    gcongr
    by_cases hr : 63 / 100 < siteRadius c' ((k : ℝ) + 1 / 2)
    · have := h2 hr
      simp only [hr, ite_true, show B ≤ (k : ℝ) from by rw [hB]; exact this]
      exact le_rfl
    · simp only [hr, ite_false]
      have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have : 0 ≤ ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
      split_ifs
      · positivity
      · exact le_rfl
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have sT : ∑ k ∈ Finset.Icc 2 n, (if siteRadius c' ((k : ℝ) + 1 / 2) ≤ 63 / 100 then
      CT * c34 * lambdaComb c' * (k : ℝ) ^ (-(4 / 3 : ℝ)) else 0) ≤ CT * c34 * lambdaComb c' * kernZ := by
    calc _ ≤ ∑ k ∈ Finset.Icc 2 n, CT * c34 * lambdaComb c' * kern k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
          rw [kern_eq_rpow hk1]
          split_ifs
          · exact le_rfl
          · have := Real.rpow_nonneg (Nat.cast_nonneg k) (-(4 / 3 : ℝ)); positivity
      _ = CT * c34 * lambdaComb c' * ∑ k ∈ Finset.Icc 2 n, kern k := by rw [Finset.mul_sum]
      _ ≤ CT * c34 * lambdaComb c' * kernZ := by
          gcongr
          calc ∑ k ∈ Finset.Icc 2 n, kern k ≤ ∑ k ∈ Finset.Icc 1 n, kern k :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.Icc_subset_Icc (by norm_num) le_rfl) (fun i _ _ => kern_nonneg i)
            _ ≤ kernZ := sum_kern_le n
  have sF : ∑ k ∈ Finset.Icc 2 n, (if B ≤ (k : ℝ) then CF * ((k : ℝ) - 3 / 4) ^ (-(2 : ℝ)) else 0) ≤
      CF * (2 / (B - 1)) := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    gcongr
    exact sum_inv_sq_tail hB2 n
  have hinv : 2 / (B - 1) ≤ 4 * κ23 * lambdaComb c' / n0 := by
    have h1 : 2 / (B - 1) ≤ 4 / (c' * n0) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    have h2 := inv_le_kTip_lambda hc'one
    calc 2 / (B - 1) ≤ 4 / (c' * n0) := h1
      _ = 4 / n0 * (1 / c') := by field_simp
      _ ≤ 4 / n0 * (κ23 * lambdaComb c') := by gcongr
      _ = _ := by ring
  have hF2 : CF * (2 / (B - 1)) ≤ CF * (4 * κ23 * lambdaComb c' / n0) := by gcongr
  have hfin : A / 24 * (CT * c34 * lambdaComb c' * kernZ + CF * (4 * κ23 * lambdaComb c' / n0)) ≤
      ((CT * c34 * kernZ + 4 * CF * κ23 / n0) / 24 + 1) * A * lambdaComb c' := by
    have : A / 24 * (CT * c34 * lambdaComb c' * kernZ + CF * (4 * κ23 * lambdaComb c' / n0)) =
        (CT * c34 * kernZ + 4 * CF * κ23 / n0) / 24 * A * lambdaComb c' := by field_simp
    rw [this]
    have : 0 ≤ A * lambdaComb c' := by positivity
    nlinarith
  calc A / 24 * (_ + _) ≤ A / 24 * (CT * c34 * lambdaComb c' * kernZ + CF * (4 * κ23 * lambdaComb c' / n0)) := by
        gcongr
        linarith
    _ ≤ _ := hfin

/-- `G` is `A`-Lipschitz on `[ξ_*, ∞)`. -/
lemma KernelHyp.lipschitz {G : ℝ → ℝ} {A : ℝ} (hG : KernelHyp G A) {y y' : ℝ} (hy : xiStar ≤ y)
    (hy' : xiStar ≤ y') : |G y - G y'| ≤ A * |y - y'| := by
  have hxs := xiStar_pos
  have hmem : ∀ t ∈ Set.uIcc y' y, xiStar ≤ t := fun t ht => by
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := G) (f' := deriv G) (C := A)
    (s := Set.uIcc y' y) (x := y') (y := y)
    (fun t ht => (hG.d1 t (by linarith [hmem t ht])).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      refine (hG.b1 t (hmem t ht)).trans ?_
      have : 0 < 1 + t := by linarith [hmem t ht]
      rw [div_le_iff₀ this]
      nlinarith [hG.nonneg, hmem t ht])
    (convex_uIcc y' y) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using key

lemma continuousOn_chiQuantile_Ici {c' : ℝ} (hc' : 0 < c') :
    ContinuousOn (chiQuantile c') (Icc (1 / 4 : ℝ) (3 / 2)) :=
  (continuousOn_chiQuantile hc').mono fun x hx => by show 1 / 4 ≤ x; exact hx.1

/-- **The head** (`rem:P1.2`(2), Step 2): `|G(χ_1) - 2 ∫_{1/4}^{3/2} G(χ_a) da + (3/2) G(ξ_*)| ≤ 5 A λ`
for `λ ≤ 1`... in fact for every `c' > 0`. -/
theorem midpoint_head_le {c' : ℝ} (hc' : 0 < c') {G : ℝ → ℝ} {A : ℝ} (hG : KernelHyp G A) :
    |G (chiQuantile c' 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), G (chiQuantile c' a)) +
      3 / 2 * G xiStar| ≤ 5 * A * lambdaComb c' := by
  have hxs := xiStar_pos
  have hA := hG.nonneg
  have hlam := (lamPos hc').le
  -- pointwise
  have hpt : ∀ a ∈ Icc (1 / 4 : ℝ) (3 / 2), |G (chiQuantile c' a) - G xiStar| ≤ 5 / 4 * (A * lambdaComb c') := by
    intro a ha
    have h1 := (chiQuantile_spec hc' ha.1).1
    have h2 := (siteRadius_bounds hc' ha.1).2
    have hΦ : phiQuantile a ≤ 5 / 4 := by
      unfold phiQuantile
      have h0 : 0 ≤ a - 1 / 4 := by linarith [ha.1]
      have h3 : a - 1 / 4 ≤ 5 / 4 := by linarith [ha.2]
      rcases le_total (a - 1 / 4) 1 with h | h
      · calc (a - 1 / 4) ^ (2 / 3 : ℝ) ≤ 1 ^ (2 / 3 : ℝ) := Real.rpow_le_rpow h0 h (by norm_num)
          _ = 1 := Real.one_rpow _
          _ ≤ 5 / 4 := by norm_num
      · calc (a - 1 / 4) ^ (2 / 3 : ℝ) ≤ (a - 1 / 4) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h (by norm_num)
          _ = a - 1 / 4 := Real.rpow_one _
          _ ≤ 5 / 4 := h3
    have hr : chiQuantile c' a - xiStar ≤ 5 / 4 * lambdaComb c' := by
      unfold siteRadius at h2
      nlinarith
    have := hG.lipschitz h1 le_rfl
    have h3 : |chiQuantile c' a - xiStar| = chiQuantile c' a - xiStar := abs_of_nonneg (by linarith)
    rw [h3] at this
    calc _ ≤ A * (chiQuantile c' a - xiStar) := this
      _ ≤ A * (5 / 4 * lambdaComb c') := by gcongr
      _ = _ := by ring
  have hcont : ContinuousOn (fun a => G (chiQuantile c' a)) (Icc (1 / 4 : ℝ) (3 / 2)) := by
    intro a ha
    have hy : 0 < chiQuantile c' a := lt_of_lt_of_le xiStar_pos (chiQuantile_spec hc' ha.1).1
    exact ((hG.d1 _ hy).continuousAt.comp_continuousWithinAt
      ((continuousOn_chiQuantile_Ici hc') a ha))
  have hint : IntervalIntegrable (fun a => G (chiQuantile c' a)) MeasureTheory.volume (1 / 4) (3 / 2) :=
    hcont.intervalIntegrable_of_Icc (by norm_num)
  have hint0 : ∫ a in (1 / 4 : ℝ)..(3 / 2), (G (chiQuantile c' a) - G xiStar) =
      (∫ a in (1 / 4 : ℝ)..(3 / 2), G (chiQuantile c' a)) - 5 / 4 * G xiStar := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hbd : |∫ a in (1 / 4 : ℝ)..(3 / 2), (G (chiQuantile c' a) - G xiStar)| ≤
      5 / 4 * (5 / 4 * (A * lambdaComb c')) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 4 : ℝ)) (b := 3 / 2)
      (f := fun a => G (chiQuantile c' a) - G xiStar) (C := 5 / 4 * (A * lambdaComb c'))
      (fun a ha => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 3 / 2)] at ha
        exact hpt a ⟨ha.1.le, ha.2⟩)
    rw [Real.norm_eq_abs] at this
    have e : |(3 / 2 : ℝ) - 1 / 4| = 5 / 4 := by norm_num [abs_of_pos]
    rw [e] at this
    linarith
  have h1 := hpt 1 ⟨by norm_num, by norm_num⟩
  have e1 : G (chiQuantile c' 1) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), G (chiQuantile c' a)) + 3 / 2 * G xiStar =
      (G (chiQuantile c' 1) - G xiStar) - 2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), (G (chiQuantile c' a) - G xiStar)) := by
    rw [hint0]; ring
  rw [e1]
  have : 0 ≤ A * lambdaComb c' := by positivity
  calc _ ≤ |G (chiQuantile c' 1) - G xiStar| + |2 * (∫ a in (1 / 4 : ℝ)..(3 / 2), (G (chiQuantile c' a) - G xiStar))| :=
        abs_sub _ _
    _ ≤ 5 / 4 * (A * lambdaComb c') + 2 * (5 / 4 * (5 / 4 * (A * lambdaComb c'))) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith
    _ ≤ _ := by nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.midpoint_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms midpoint_sum_le

end FormalResearch.ModularBootstrap.Upper.Ramped
