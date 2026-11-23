module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernelBounds

/-!
# The Langer chart of the comb transfer: Proposition 1.2(1) and the inputs `(F1)`, `(F2)` of Proposition 1.2(2)

`remainder.tex`, Proposition 1.2 (`rem:P1.2`).  This module collects the unconditional interface that the
quantitative comb-to-Airy identity (Proposition 1.2(2)) consumes.

* **Proposition 1.2(1)**: `langerTau_spec` (`LangerTauSpec`): `τ` is `C^m` on `(0, ∞)` for every `m` (the paper's
  real-analytic claim is weakened to smooth: all uses are bounds on `τ, τ', τ'', τ'''`), `τ(ξ_*) = 0`,
  `τ'(ξ_*) = 1`, `τ' > 0`, `N = k_tip τ^{3/2}` (`x ≥ ξ_*`), `-(U + L) = 2π k_tip |τ|^{3/2}` (`0 < x ≤ ξ_*`).
* Inverse and sites: `langerTauInv`, `langerTauInv_expansion` (`τ^{-1}(s) = ξ_* + s + O(s²)`),
  `chiQuantile_eq_langerTauInv` (`χ_a = τ^{-1}(λ Φ_a)`), `langerTau_chiQuantile` (`τ(χ_a) = λ Φ_a`).
* **`(F1)`**: `langerChart_F1` below.
* **`(F2)`**: `langerChart_F2` below (`langerK`, `langerQ2`, `langerQ2_diag`, `realLogT_eq_log_add_langerK`,
  `langerK_xiStar`, `langerK_deriv_bounds`).

Relation to the lower-side Langer chart (`ConcreteBootstrap.LangerChart`): that chart is the local complex
analytic inverse `virasoroXiInf` of `ũ_∞` in the variable `ξ = x²/3`, obtained from the inverse function
theorem (no explicit formula, no global range); its real restriction is `c'^{2/3} β τ` up to the change of
variable, by `virasoro_chart_potential_eq`, but it is local and non-explicit, so the comb coordinate `τ` is
defined independently here (explicit, global on `(0, ∞)`, with the identity `N = k_tip τ^{3/2}`).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-- **`(F1)`**: the Langer coordinate and the site map.
(1) `τ' ≥ c_τ > 0` on `[ξ_*/2, ∞)`;
(2) `|τ'|, |τ''| ≤ C` on every compact `[a, b] ⊂ (0, ∞)`;
(3) for `y ≥ ξ_* + r₁`: `τ'(y) ≤ C τ(y)/(1+y)` and `|τ''(y)| ≤ C τ(y)/(1+y)²` (`τ ≍ y^{4/3}`; `τ'` is
not bounded on `[ξ_*/2, ∞)`);
(4) `ℓ_k ≍ λ k^{-1/3}` while `χ_k - ξ_* ≤ 0.63` (`c' ≥ c₀`);
(5) `(log ρ_U)'(ξ_* + r) ≤ 1/(2r) + π/(4√2)` (`logDeriv_rhoU_tip_bounds`) and
`χ_a'^2 (1 + (log ρ_U)'(χ_a)) ≤ C λ a^{-4/3}` for `a ≥ 1`, `χ_a - ξ_* ≤ 0.63`;
(6) for `χ_a ≥ ξ_* + r₁`: `χ_a' ≤ C/(c'(1 + χ_a))` and `(log ρ_U)'(χ_a) ≤ C/(1 + χ_a)`.
(The tip bounds `χ_a - ξ_* ≤ λ(a - 1/4)^{2/3}`, `χ_a' ≤ C λ a^{-1/3}` and `ℓ_k ≤ ℓ_1 ≤ C λ` are
`siteRadius_bounds`, `quantile_tip_bounds`, `siteGap_eventually_le` of `Upper.Comb`.) -/
theorem langerChart_F1 :
    (∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, xiStar / 2 ≤ x → c ≤ deriv langerTau x) ∧
    (∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ x ∈ Icc a b,
      |deriv langerTau x| ≤ C ∧ |deriv (deriv langerTau) x| ≤ C) ∧
    (∀ r1 : ℝ, 0 < r1 → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, xiStar + r1 ≤ y →
      0 < langerTau y ∧ deriv langerTau y ≤ C * langerTau y / (1 + y) ∧
        |deriv (deriv langerTau) y| ≤ C * langerTau y / (1 + y) ^ 2) ∧
    (∃ c C c0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < c0 ∧ ∀ c' : ℝ, c0 ≤ c' → ∀ k : ℕ, 1 ≤ k →
      siteRadius c' k ≤ 63 / 100 →
      c * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ)) ≤ siteGap c' k ∧
        siteGap c' k ≤ C * lambdaComb c' * (k : ℝ) ^ (-(1 / 3 : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 0 < c' → ∀ a : ℝ, 1 ≤ a → siteRadius c' a ≤ 63 / 100 →
      chiDeriv c' a ^ 2 * (1 + rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a)) ≤
        C * lambdaComb c' * a ^ (-(4 / 3 : ℝ))) ∧
    (∀ r1 : ℝ, 0 < r1 → ∃ C : ℝ, 0 < C ∧ ∀ c' : ℝ, 0 < c' → ∀ a : ℝ,
      xiStar + r1 ≤ chiQuantile c' a → chiDeriv c' a ≤ C / (c' * (1 + chiQuantile c' a))) ∧
    (∀ r1 : ℝ, 0 < r1 → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, xiStar + r1 ≤ y →
      rhoUDeriv y / rhoU y ≤ C / (1 + y)) :=
  ⟨langerTau_deriv_ge_const, fun _ b ha => langerTau_deriv_bound_compact (b := b) ha,
    fun _ hr1 => langerTau_large hr1, siteGap_two_sided, chiDeriv_sq_logDeriv_le,
    fun _ hr1 => chiDeriv_large_le hr1, fun _ hr1 => logDeriv_rhoU_large_le hr1⟩

/-- **`(F2)`**: the smooth part of the site weight.  `Q(x,y) = T(x-y)/D(x,y)` (`langerQ2`) is positive and
smooth, equals `tanh(π(x-y)/2)/(τ(x) - τ(y))` for `y ≠ x` and `π/(2τ'(x))` on the diagonal;
`f_x(y) = log|τ(x) - τ(y)| + K(x,y)`, `K = log Q + log tanh(π(x+y)/2)` is `C^m` in `y`, `K(x, ξ_*) = K_*(x)`
and `|∂_y^j K(x,y)| ≤ C (1+y)^{-j}` (`j = 1, 2`) uniformly for `x ∈ [ξ_*/2, ξ_* + r₀]`, `y ≥ ξ_*`. -/
theorem langerChart_F2 :
    (∀ x y : ℝ, 0 < x → 0 < y → 0 < langerQ2 x y) ∧
    (∀ x : ℝ, langerQ2 x x = π / (2 * deriv langerTau x)) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → y ≠ x →
      langerQ2 x y = Real.tanh (π * (x - y) / 2) / (langerTau x - langerTau y)) ∧
    (∀ x y : ℝ, 0 < x → 0 < y → y ≠ x →
      realLogT x y = Real.log |langerTau x - langerTau y| + langerK x y) ∧
    (∀ (m : ℕ) (x : ℝ), 0 < x → ContDiffOn ℝ m (langerK x) (Ioi 0)) ∧
    (∀ x : ℝ, 0 < x → x ≠ xiStar → langerK x xiStar = Real.log (Real.tanh (π * |x - xiStar| / 2) *
      Real.tanh (π * (x + xiStar) / 2) / |langerTau x|)) ∧
    (∀ r0 : ℝ, 0 < r0 → ∃ C : ℝ, 0 < C ∧ ∀ x ∈ langerX r0, ∀ y : ℝ, xiStar ≤ y →
      |deriv (langerK x) y| ≤ C / (1 + y) ∧ |deriv (deriv (langerK x)) y| ≤ C / (1 + y) ^ 2) :=
  ⟨fun _ _ hx hy => langerQ2_pos hx hy, fun _ => langerQ2_diag,
    fun _ _ hx hy hxy => langerQ2_of_ne hx hy hxy,
    fun _ _ hx hy hxy => realLogT_eq_log_add_langerK hx hy hxy,
    fun m _ hx => contDiffOn_langerK m hx, fun _ hx hxs => langerK_xiStar hx hxs,
    fun r0 hr0 => langerK_deriv_bounds r0 hr0⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerChart_F1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerChart_F1

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerChart_F2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerChart_F2

end FormalResearch.ModularBootstrap.Upper.Ramped
