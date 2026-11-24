module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoLevelLower
public import FormalResearch.ModularBootstrap.TwoLevel.SoftEdgeA2StarLipschitz

/-!
# Theorem SE.7: the two-level lower rate with a moving first level (`soft_edge_two_level_stability.tex`, `se:3.2`)

Source: `CFT/modular_bootstrap/paper/soft_edge_two_level_stability.tex`, Theorem SE.7 (`se:3.2`), a corollary of
Theorem `W1'(2)` (`theorem_W1prime_two`) at the first level `A' = (t_* - ξ̄ c')/c'^{1/3}`, the monotonicity of `A_2^*`
(`A2star_strictMonoOn`) and its Lipschitz bound (`A2star_lipschitzOn`).

Notation: the spinless Virasoro test class `Ā` at central charge `c` is `virasoroProblem` at `a = c'/12`, `c' = c - 1`;
the hypotheses "nonzero `g ∈ Ā`, `g_vac ≥ 0`, `g ≥ 0` on `[τ, ∞)`" are `virasoroProblem.IsWeaklyFeasible (c'/12) τ g`.

* `theorem_SE7_uniform`: for `K ⊆ (-∞, A_opt)` compact, `η > 0` and `M < A_opt` with `A₁ + η ≤ M` on `K`, and `C₁ ≥ 0`, there
  are `c₁, C_-` such that for all `A₁ ∈ K` and `c' ≥ c₁`, every such `g` with `g(t_*) ≥ 0` at some
  `t_* ∈ [ξ̄ c' + A₁ c'^{1/3} - C₁ log c', ξ̄ c' + (A₁ + η) c'^{1/3}]` has
  `τ ≥ ξ̄ c' + A_2^*(A₁) c'^{1/3} - C_- log c'`, and if `C₁ = 0` even `τ ≥ ξ̄ c' + A_2^*(A₁) c'^{1/3} - C_-`;
* `theorem_SE7`: the fixed-`A₁` statement of the paper (`K = {A₁}`, `M = A₁ + η`).

The paper states the threshold in `c` with `c' = c - 1`; here every statement is in `c'` (the window is in `c'`), so
"for all `c ≥ c₁`" reads "for all `c' ≥ c₁`".
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special Crossing

/-- Eventually `C₁ log c' ≤ c'^{1/3}`, and `c' ≥ 3`. -/
lemma eventually_log_le_rpow (C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ c₃ : ℝ, 3 ≤ c₃ ∧ ∀ c' : ℝ, c₃ ≤ c' → C₁ * Real.log c' ≤ c' ^ (1 / 3 : ℝ) := by
  have hε : 0 < 1 / (C₁ + 1) := by positivity
  have h := ((isLittleO_log_rpow_atTop (r := 1 / 3) (by norm_num)).bound hε).and
    (eventually_ge_atTop (3 : ℝ))
  obtain ⟨c₃, hc₃⟩ := eventually_atTop.mp h
  refine ⟨max c₃ 3, le_max_right _ _, fun c' hc' => ?_⟩
  obtain ⟨hb, h3⟩ := hc₃ c' ((le_max_left _ _).trans hc')
  have hc'0 : 0 < c' := by linarith
  have hlog : 0 ≤ Real.log c' := Real.log_nonneg (by linarith)
  have hp : 0 ≤ c' ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc'0.le _
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hp, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at hb
  nlinarith [mul_nonneg hC₁ hlog]

lemma one_le_log_of_three_le {c' : ℝ} (h : 3 ≤ c') : 1 ≤ Real.log c' := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

/-- **Theorem SE.7** (`se:3.2`), uniform for the first level in a compact subset `K` of `(-∞, A_opt)`. -/
theorem theorem_SE7_uniform {K : Set ℝ} (hK : IsCompact K) {η M C₁ : ℝ} (hη : 0 < η) (hM : M < Aopt)
    (hKM : ∀ A ∈ K, A + η ≤ M) (hC₁ : 0 ≤ C₁) :
    ∃ c₁ C_minus : ℝ, ∀ A₁ ∈ K, ∀ c' : ℝ, c₁ ≤ c' → ∀ (τ : ℝ) (g : ℝ → ℝ) (t_star : ℝ),
      xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ) - C₁ * Real.log c' ≤ t_star →
      t_star ≤ xiBar * c' + (A₁ + η) * c' ^ (1 / 3 : ℝ) →
      0 ≤ g t_star → virasoroProblem.IsWeaklyFeasible (c' / 12) τ g →
      xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - C_minus * Real.log c' ≤ τ ∧
      (C₁ = 0 → xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - C_minus ≤ τ) := by
  obtain ⟨lo, hlo⟩ := hK.bddBelow
  have hJc : IsCompact (Icc (lo - 1) M) := isCompact_Icc
  have hJsub : Icc (lo - 1) M ⊆ Iio Aopt := fun x hx => lt_of_le_of_lt hx.2 hM
  obtain ⟨c₂, D₂, hW⟩ := theorem_W1prime_two virasoroProblem (R_off := 0) le_rfl hJc hJsub
  obtain ⟨L, hL0, hL⟩ := A2star_lipschitzOn hJc hJsub
  obtain ⟨c₃, hc₃3, hc₃⟩ := eventually_log_le_rpow C₁ hC₁
  set D : ℝ := max D₂ 0 with hD
  have hD0 : 0 ≤ D := le_max_right _ _
  have hDD : D₂ ≤ D := le_max_left _ _
  refine ⟨max c₂ c₃, D + L * C₁, fun A₁ hA₁ c' hc' τ g t_star hlow hup hg hwf => ?_⟩
  have hcc₂ : c₂ ≤ c' := (le_max_left _ _).trans hc'
  have hcc₃ : c₃ ≤ c' := (le_max_right _ _).trans hc'
  have hc'0 : 0 < c' := by linarith
  have hu : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'0 _
  have hlog1 : 1 ≤ Real.log c' := one_le_log_of_three_le (by linarith)
  have hCl : C₁ * Real.log c' ≤ c' ^ (1 / 3 : ℝ) := hc₃ c' hcc₃
  set u : ℝ := c' ^ (1 / 3 : ℝ) with hu_def
  set A' : ℝ := (t_star - xiBar * c') / u with hA'
  have ht : t_star = xiBar * c' + A' * u := by
    have : A' * u = t_star - xiBar * c' := by rw [hA']; exact div_mul_cancel₀ _ hu.ne'
    linarith
  have hA'lo : A₁ * u - C₁ * Real.log c' ≤ A' * u := by linarith
  have hA'up : A' * u ≤ (A₁ + η) * u := by linarith
  have hA₁M : A₁ + η ≤ M := hKM A₁ hA₁
  have hA'M : A' ≤ M := by
    have : A' * u ≤ (A₁ + η) * u := hA'up
    have := le_of_mul_le_mul_right this hu
    linarith
  have hA₁lo : lo ≤ A₁ := hlo hA₁
  have hA'lo' : lo - 1 ≤ A' := by
    have h1 : (A₁ - 1) * u ≤ A' * u := by nlinarith
    have := le_of_mul_le_mul_right h1 hu
    linarith
  have hA'J : A' ∈ Icc (lo - 1) M := ⟨hA'lo', hA'M⟩
  have hA₁J : A₁ ∈ Icc (lo - 1) M := ⟨by linarith, by linarith⟩
  have hw1 := hW A' hA'J c' hcc₂ τ g t_star (by rw [abs_nonpos_iff]; linarith) hg hwf
  rw [← hu_def] at hw1
  have hkey : A2star A₁ * u - L * (C₁ * Real.log c') ≤ A2star A' * u := by
    rcases le_total A₁ A' with h | h
    · have hm : A2star A₁ ≤ A2star A' :=
        A2star_strictMonoOn.monotoneOn (hJsub hA₁J) (hJsub hA'J) h
      have : 0 ≤ L * (C₁ * Real.log c') := by
        have : 0 ≤ Real.log c' := by linarith
        positivity
      nlinarith [mul_le_mul_of_nonneg_right hm hu.le]
    · have hl := hL A₁ hA₁J A' hA'J
      rw [abs_of_nonneg (by linarith : 0 ≤ A₁ - A')] at hl
      have h1 : A2star A₁ - A2star A' ≤ L * (A₁ - A') := (le_abs_self _).trans hl
      have h2 : (A₁ - A') * u ≤ C₁ * Real.log c' := by linarith
      have h3 : L * ((A₁ - A') * u) ≤ L * (C₁ * Real.log c') := mul_le_mul_of_nonneg_left h2 hL0
      have h4 : (A2star A₁ - A2star A') * u ≤ L * (A₁ - A') * u :=
        mul_le_mul_of_nonneg_right h1 hu.le
      nlinarith
  constructor
  · nlinarith [mul_nonneg hD0 (by linarith : 0 ≤ Real.log c' - 1)]
  · intro hC0
    subst hC0
    simp only [mul_zero, zero_mul, add_zero, sub_zero] at hkey ⊢
    linarith

/-- **Theorem SE.7** (`se:3.2`) as stated in the paper: fixed `η > 0` and `A₁` with `A₁ + η < A_opt` (so `A₁ < A_opt`), `C₁ ≥ 0`. -/
theorem theorem_SE7 {A₁ η C₁ : ℝ} (hη : 0 < η) (hAη : A₁ + η < Aopt) (hC₁ : 0 ≤ C₁) :
    ∃ c₁ C_minus : ℝ, ∀ c' : ℝ, c₁ ≤ c' → ∀ (τ : ℝ) (g : ℝ → ℝ) (t_star : ℝ),
      xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ) - C₁ * Real.log c' ≤ t_star →
      t_star ≤ xiBar * c' + (A₁ + η) * c' ^ (1 / 3 : ℝ) →
      0 ≤ g t_star → virasoroProblem.IsWeaklyFeasible (c' / 12) τ g →
      xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - C_minus * Real.log c' ≤ τ ∧
      (C₁ = 0 → xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - C_minus ≤ τ) := by
  obtain ⟨c₁, C, h⟩ := theorem_SE7_uniform (K := {A₁}) isCompact_singleton hη hAη
    (by simp) hC₁
  exact ⟨c₁, C, fun c' hc' => h A₁ rfl c' hc'⟩

end FormalResearch.ModularBootstrap.TwoLevel

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_SE7_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.theorem_SE7_uniform

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_SE7' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.theorem_SE7
