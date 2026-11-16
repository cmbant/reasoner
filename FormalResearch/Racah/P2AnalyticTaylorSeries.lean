module

public import Mathlib

/-!
# Taylor series at `0` as a ring homomorphism on smooth germs (Weyl P2 analytic half, auxiliary)

`taylorSer f = ∑_n (f^{(n)}(0)/n!) t^n ∈ ℝ⟦t⟧`.  On functions `ℝ → ℝ` smooth at `0` it is additive and
multiplicative (Leibniz), sends constants to constants and `t ↦ t` to `X`, and depends only on the germ of
`f` at `0`.  The coefficients of `taylorSer (fun t => G x t)` are the `taylorCoeff`s of
`P2AnalyticTaylor` (`taylorCoeff_eq_coeff_taylorSer`), so recurrences that hold identically in `t` hold
coefficientwise as identities of formal power series.  This is the passage from "the closed form satisfies
the rank recurrence identically, so its Taylor coefficients satisfy it order by order" (paper,
proof of `thm:3jNLO` and `app:localgeneral`, *Link to the physical kernels*) to formal series.
-/

@[expose] public section

namespace FormalResearch.Racah

open scoped ContDiff
open Filter

/-- The formal Taylor series at `0`. -/
noncomputable def taylorSer (f : ℝ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => iteratedDeriv n f 0 / (n.factorial : ℝ)

lemma coeff_taylorSer (f : ℝ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorSer f) = iteratedDeriv n f 0 / (n.factorial : ℝ) := by
  simp [taylorSer, PowerSeries.coeff_mk]

/-- Smooth germs at `0`. -/
abbrev SmoothAt0 (f : ℝ → ℝ) : Prop := ContDiffAt ℝ ∞ f 0

lemma SmoothAt0.of_contDiff {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) : SmoothAt0 f := h.contDiffAt

lemma SmoothAt0.mul {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    SmoothAt0 (fun t => f t * g t) := ContDiffAt.mul hf hg

lemma SmoothAt0.add {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    SmoothAt0 (fun t => f t + g t) := ContDiffAt.add hf hg

lemma SmoothAt0.sub {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    SmoothAt0 (fun t => f t - g t) := ContDiffAt.sub hf hg

lemma SmoothAt0.const (c : ℝ) : SmoothAt0 (fun _ => c) := contDiffAt_const

lemma SmoothAt0.id : SmoothAt0 (fun t => t) := contDiffAt_id

/-- Leibniz: the Taylor series is multiplicative. -/
theorem taylorSer_mul {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    taylorSer (fun t => f t * g t) = taylorSer f * taylorSer g := by
  ext n
  have hf' : ContDiffAt ℝ (n : WithTop ℕ∞) f 0 := hf.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffAt ℝ (n : WithTop ℕ∞) g 0 := hg.of_le (by exact_mod_cast le_top)
  have h := iteratedDeriv_fun_mul (n := n) hf' hg'
  rw [PowerSeries.coeff_mul, coeff_taylorSer, h, Finset.sum_div]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_taylorSer]
  rw [Nat.cast_choose ℝ hi']
  have : ((n - i).factorial : ℝ) ≠ 0 := by positivity
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem taylorSer_add {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    taylorSer (fun t => f t + g t) = taylorSer f + taylorSer g := by
  ext n
  have hf' : ContDiffAt ℝ (n : WithTop ℕ∞) f 0 := hf.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffAt ℝ (n : WithTop ℕ∞) g 0 := hg.of_le (by exact_mod_cast le_top)
  rw [map_add, coeff_taylorSer, coeff_taylorSer, coeff_taylorSer, iteratedDeriv_fun_add hf' hg', add_div]

theorem taylorSer_sub {f g : ℝ → ℝ} (hf : SmoothAt0 f) (hg : SmoothAt0 g) :
    taylorSer (fun t => f t - g t) = taylorSer f - taylorSer g := by
  ext n
  have hf' : ContDiffAt ℝ (n : WithTop ℕ∞) f 0 := hf.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffAt ℝ (n : WithTop ℕ∞) g 0 := hg.of_le (by exact_mod_cast le_top)
  rw [map_sub, coeff_taylorSer, coeff_taylorSer, coeff_taylorSer, iteratedDeriv_fun_sub hf' hg', sub_div]

theorem taylorSer_const (c : ℝ) : taylorSer (fun _ => c) = PowerSeries.C c := by
  ext n
  rw [coeff_taylorSer, PowerSeries.coeff_C]
  cases n with
  | zero => simp
  | succ n => simp [iteratedDeriv_const]

theorem taylorSer_id : taylorSer (fun t => t) = PowerSeries.X := by
  ext n
  rw [coeff_taylorSer, PowerSeries.coeff_X]
  rw [iteratedDeriv_fun_id_zero]
  by_cases h : n = 1
  · subst h; simp
  · simp [h]

theorem taylorSer_C_mul {f : ℝ → ℝ} (hf : SmoothAt0 f) (c : ℝ) :
    taylorSer (fun t => c * f t) = PowerSeries.C c * taylorSer f := by
  rw [taylorSer_mul (SmoothAt0.const c) hf, taylorSer_const]

/-- The Taylor series only depends on the germ at `0`. -/
theorem taylorSer_congr {f g : ℝ → ℝ} (h : f =ᶠ[nhds 0] g) : taylorSer f = taylorSer g := by
  ext n
  rw [coeff_taylorSer, coeff_taylorSer, h.iteratedDeriv_eq]

lemma taylorSer_one : taylorSer (fun _ => (1 : ℝ)) = 1 := by
  rw [taylorSer_const]; rfl

/-- `taylorCoeff` of `P2AnalyticTaylor` is the coefficient of the formal Taylor series. -/
lemma taylor_coeff_eq (f : ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n f 0 / (n.factorial : ℝ) = PowerSeries.coeff n (taylorSer f) :=
  (coeff_taylorSer f n).symm

end FormalResearch.Racah
