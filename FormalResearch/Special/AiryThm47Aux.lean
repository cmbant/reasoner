module

public import FormalResearch.Special.AiryPolyApplications
public import FormalResearch.Special.AiryThm47Nonintegrability

/-!
# Auxiliary facts for Theorem 4.7: local minima and the product `∏(z - t)`

* `at47_deriv_eq_zero_of_min`: a function that is entire, real on `ℝ`, `≥ 0` on `(-∞, u]` and vanishes at `x < u` has `f'(x) = 0`.
* `at47_pr S z = ∏_{t ∈ S}(z - t)`, its value on `ℝ`, nonvanishing off `S`, its sign below `S`, and `pr'(t) ≠ 0` for `t ∈ S`.
All proved.
-/

@[expose] public section

open Complex Polynomial Filter Topology

namespace FormalResearch.Special

lemma at47_deriv_eq_zero_of_min {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0)
    {x u : ℝ} (hxu : x < u) (hnn : ∀ y : ℝ, y ≤ u → 0 ≤ (f (y : ℂ)).re) (h0 : f (x : ℂ) = 0) :
    deriv f (x : ℂ) = 0 := by
  have hd : HasDerivAt f (deriv f (x : ℂ)) (x : ℂ) := (hf (x : ℂ)).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => (f (y : ℂ)).re) (deriv f (x : ℂ)).re x := hd.real_of_complex
  have hmin : IsLocalMin (fun y : ℝ => (f (y : ℂ)).re) x := by
    filter_upwards [Iio_mem_nhds hxu] with y hy
    rw [h0]; simpa using hnn y (le_of_lt hy)
  have hre := hmin.hasDerivAt_eq_zero h1
  have h2 : HasDerivAt (fun y : ℝ => f (y : ℂ)) (deriv f (x : ℂ)) x := hd.comp_ofReal
  have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h2
  have h4 : (Complex.imCLM ∘ fun y : ℝ => f (y : ℂ)) = fun _ => (0 : ℝ) := by
    funext y; simp [hreal y]
  rw [h4] at h3
  have him : (0 : ℝ) = Complex.imCLM (deriv f (x : ℂ)) := (hasDerivAt_const x (0 : ℝ)).unique h3
  apply Complex.ext
  · simpa using hre
  · simpa using him.symm

/-- The product `∏_{t ∈ S}(z - t)`. -/
noncomputable def at47_pr (S : Finset ℝ) (z : ℂ) : ℂ := ∏ t ∈ S, (z - (t : ℂ))

lemma at47_pr_differentiable (S : Finset ℝ) : Differentiable ℂ (at47_pr S) := by
  unfold at47_pr; fun_prop

lemma at47_pr_eq_zero {S : Finset ℝ} {t : ℝ} (ht : t ∈ S) : at47_pr S (t : ℂ) = 0 :=
  Finset.prod_eq_zero ht (sub_self _)

lemma at47_pr_ne_zero {S : Finset ℝ} {x : ℝ} (hx : x ∉ S) : at47_pr S (x : ℂ) ≠ 0 := by
  unfold at47_pr
  rw [Finset.prod_ne_zero_iff]
  intro t ht h0
  have : x = t := by exact_mod_cast sub_eq_zero.mp h0
  exact hx (this ▸ ht)

lemma at47_pr_ofReal (S : Finset ℝ) (x : ℝ) : at47_pr S (x : ℂ) = ((∏ t ∈ S, (x - t) : ℝ) : ℂ) := by
  unfold at47_pr; push_cast; rfl

lemma at47_pr_sign {S : Finset ℝ} {x : ℝ} (hx : ∀ t ∈ S, x ≤ t) :
    0 ≤ (-1 : ℝ) ^ S.card * ∏ t ∈ S, (x - t) := by
  have : (-1 : ℝ) ^ S.card * ∏ t ∈ S, (x - t) = ∏ t ∈ S, (t - x) := by
    rw [← Finset.prod_const (b := (-1 : ℝ)) (s := S), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => by ring
  rw [this]
  exact Finset.prod_nonneg fun t ht => by linarith [hx t ht]

lemma at47_pr_deriv_ne_zero {S : Finset ℝ} {t : ℝ} (ht : t ∈ S) : deriv (at47_pr S) (t : ℂ) ≠ 0 := by
  classical
  have hfac : ∀ z, at47_pr S z = (z - (t : ℂ)) * at47_pr (S.erase t) z := by
    intro z; unfold at47_pr
    rw [← Finset.mul_prod_erase S (fun s => z - (s : ℂ)) ht]
  have h1 : at47_pr S = fun z => (z - (t : ℂ)) * at47_pr (S.erase t) z := funext hfac
  rw [h1]
  have hd := (hasDerivAt_id (t : ℂ)).sub_const (t : ℂ) |>.mul ((at47_pr_differentiable (S.erase t)) (t : ℂ)).hasDerivAt
  have hd' : HasDerivAt (fun z => (z - (t : ℂ)) * at47_pr (S.erase t) z)
      (1 * at47_pr (S.erase t) (t : ℂ) + ((t : ℂ) - (t : ℂ)) * deriv (at47_pr (S.erase t)) (t : ℂ)) (t : ℂ) := hd
  rw [hd'.deriv]
  simp only [sub_self, zero_mul, one_mul, add_zero]
  exact at47_pr_ne_zero (S := S.erase t) (x := t) (by simp)

end FormalResearch.Special
