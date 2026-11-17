module

public import FormalResearch.Special.AiryCftSignEquality
public import FormalResearch.Complex.EntireDivSq

/-!
# Theorem B at `u₁ = a₁`: double zeros and the entire quotient `(u - a₁) f / Ai²`

CFT `AIRY_POISSON.md` §4, Theorem B′, Proof 2, step 4 (second half).  Let `f` be in the class of `AiryCftSignUncertainty` (entire,
real on `ℝ`), `f ≥ 0` on `(-∞, a₁]`, and suppose all samples vanish, `f(a_n) = 0`
(`airy_sign_equality_samples`).  Then (**proved**):

* `airy_eq_deriv_zero`: `f'(a_n) = 0` for `n ≥ 2` (`a_n` is an interior minimum of the real function `Re f` on the band);
* `airy_eq_div` : `k(u) := (u - a₁) f(u)` vanishes to second order at every zero of `Ai` (at `a₁` because `f(a₁) = 0` and the factor
  `u - a₁` vanishes; at `a_n`, `n ≥ 2`, because `f(a_n) = f'(a_n) = 0`), and the zeros of `Ai` are simple, so `k = H · Ai²` for an
  **entire** `H` (generic division lemma `FormalResearch.EntireDiv.entire_exists_div_sq`).

(The note multiplies by nothing and speaks of "`h = f/Ai²` has at most a simple pole at `a₁`"; `H = (u - a₁) h` is the same statement
with the pole removed.)  The growth of `H` on the good circles, Liouville and the `L¹` argument are `AiryCftSignEqualityMain`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Double zeros.**  `f` entire, real on `ℝ`, `f ≥ 0` on `(-∞, a₁]`, `f(a_n) = 0` with `n ≥ 2`: then `f'(a_n) = 0`. -/
lemma airy_eq_deriv_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re) {n : ℕ} (hn : 2 ≤ n) (h0 : f (airyZero n : ℂ) = 0) :
    deriv f (airyZero n : ℂ) = 0 := by
  set a : ℝ := airyZero n with ha
  have h1 : HasDerivAt (fun x : ℝ => f (x : ℂ)) (deriv f (a : ℂ)) a :=
    (hf (a : ℂ)).hasDerivAt.comp_ofReal
  have hre : HasDerivAt (fun x : ℝ => (f (x : ℂ)).re) (deriv f (a : ℂ)).re a := (hf (a : ℂ)).hasDerivAt.real_of_complex
  have him0 : (deriv f (a : ℂ)).im = 0 := by
    have h2 : HasDerivAt (fun x : ℝ => (((f (x : ℂ)).re : ℝ) : ℂ)) (((deriv f (a : ℂ)).re : ℝ) : ℂ) a :=
      hre.ofReal_comp
    have h3 : (fun x : ℝ => (((f (x : ℂ)).re : ℝ) : ℂ)) = fun x : ℝ => f (x : ℂ) :=
      funext fun x => (airy_real_cast hreal x).symm
    rw [h3] at h2
    have := h1.unique h2
    rw [this]; simp
  have hlt : a < airyZero 1 := by
    have := airyZero_lt_of_lt (n := 1) (m := n) le_rfl (by omega)
    exact this
  have hmin : IsLocalMin (fun x : ℝ => (f (x : ℂ)).re) a := by
    have hnhds : Iio (airyZero 1) ∈ 𝓝 a := Iio_mem_nhds hlt
    filter_upwards [hnhds] with x hx
    have h00 : (f (a : ℂ)).re = 0 := by rw [ha, h0]; simp
    rw [h00]
    exact hpos x hx.le
  have hre0 : (deriv f (a : ℂ)).re = 0 := by
    have := hmin.hasDerivAt_eq_zero hre
    exact this
  exact Complex.ext hre0 him0

/-- **`(u - a₁) f(u) = H(u) Ai(u)²` with `H` entire.**  Under the equality hypotheses of Theorem B. -/
theorem airy_eq_div {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    (hpos : ∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re) (hs : ∀ n : ℕ, 1 ≤ n → f (airyZero n : ℂ) = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ u : ℂ, (u - (airyZero 1 : ℂ)) * f u = H u * airyAiC u ^ 2 := by
  have hk : Differentiable ℂ (fun u : ℂ => (u - (airyZero 1 : ℂ)) * f u) := by
    fun_prop
  refine EntireDiv.entire_exists_div_sq hk differentiable_airyAiC (fun z hz => ?_)
  obtain ⟨n, hn, rfl⟩ := (airyAiC_eq_zero_iff z).1 hz
  have hfn := hs n hn
  have hder : deriv (fun u : ℂ => (u - (airyZero 1 : ℂ)) * f u) (airyZero n : ℂ) = 0 := by
    have hd : HasDerivAt (fun u : ℂ => (u - (airyZero 1 : ℂ)) * f u)
        (1 * f (airyZero n : ℂ) + ((airyZero n : ℂ) - (airyZero 1 : ℂ)) * deriv f (airyZero n : ℂ)) (airyZero n : ℂ) :=
      ((hasDerivAt_id _).sub_const _).mul (hf _).hasDerivAt
    rw [hd.deriv, hfn]
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; simp
    · rw [airy_eq_deriv_zero hf hreal hpos h hfn]; simp
  refine ⟨by simp [hfn], hder, ?_⟩
  rw [deriv_airyAiC_ofReal]
  intro h
  have h' : airyAi' (airyZero n) = 0 := by exact_mod_cast h
  have := airyKer_pos' (airyZero n)
  rw [airyAi_airyZero, h'] at this
  norm_num at this

/-- info: 'FormalResearch.Special.airy_eq_deriv_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_eq_deriv_zero

/-- info: 'FormalResearch.Special.airy_eq_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_eq_div

end FormalResearch.Special
