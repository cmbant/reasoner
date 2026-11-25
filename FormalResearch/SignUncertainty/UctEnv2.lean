module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# `Env2`: `C²` functions `ℝ → ℂ` with a common envelope for `f, f', f''` (F2a helper)

`Env2 f P`: `f` is `C²` and `‖f τ‖, ‖f' τ‖, ‖f'' τ‖ ≤ P τ` for all `τ`.  Used to assemble the (M3) edge-trace bounds of
products (Leibniz): `Env2.mul` gives the envelope `4 P Q` of a product, `Env2.const_mul`, `Env2.mono`.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.SignUncertainty

/-- `f` is `C²` with `‖f‖, ‖f'‖, ‖f''‖ ≤ P`. -/
def Env2 (f : ℝ → ℂ) (P : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ∀ τ : ℝ, ‖f τ‖ ≤ P τ ∧ ‖deriv f τ‖ ≤ P τ ∧ ‖deriv (deriv f) τ‖ ≤ P τ

lemma Env2.mono {f : ℝ → ℂ} {P Q : ℝ → ℝ} (h : Env2 f P) (hPQ : ∀ τ, P τ ≤ Q τ) : Env2 f Q :=
  ⟨h.1, fun τ => ⟨(h.2 τ).1.trans (hPQ τ), (h.2 τ).2.1.trans (hPQ τ), (h.2 τ).2.2.trans (hPQ τ)⟩⟩

lemma Env2.differentiable {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) : Differentiable ℝ f :=
  h.1.differentiable (by norm_num)

lemma Env2.deriv_contDiff {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) : ContDiff ℝ 1 (deriv f) := by
  have h2 : ContDiff ℝ ((1 : ℕ) + 1) f := by simpa [one_add_one_eq_two] using h.1
  exact ((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2).2.2

lemma Env2.differentiable_deriv {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) : Differentiable ℝ (deriv f) :=
  h.deriv_contDiff.differentiable (by norm_num)

lemma Env2.mul {f g : ℝ → ℂ} {P Q : ℝ → ℝ} (hf : Env2 f P) (hg : Env2 g Q) :
    Env2 (fun τ => f τ * g τ) (fun τ => 4 * P τ * Q τ) := by
  have hP : ∀ τ, 0 ≤ P τ := fun τ => (norm_nonneg _).trans (hf.2 τ).1
  have hQ : ∀ τ, 0 ≤ Q τ := fun τ => (norm_nonneg _).trans (hg.2 τ).1
  have hd1 : deriv (fun τ => f τ * g τ) = fun τ => deriv f τ * g τ + f τ * deriv g τ := by
    funext τ
    exact deriv_mul (hf.differentiable τ) (hg.differentiable τ)
  have hd2 : deriv (deriv (fun τ => f τ * g τ)) =
      fun τ => deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ := by
    rw [hd1]
    funext τ
    have h1 : DifferentiableAt ℝ (fun τ => deriv f τ * g τ) τ :=
      (hf.differentiable_deriv τ).mul (hg.differentiable τ)
    have h2 : DifferentiableAt ℝ (fun τ => f τ * deriv g τ) τ :=
      (hf.differentiable τ).mul (hg.differentiable_deriv τ)
    have e : deriv (fun τ => deriv f τ * g τ + f τ * deriv g τ) τ =
        deriv (fun τ => deriv f τ * g τ) τ + deriv (fun τ => f τ * deriv g τ) τ :=
      (HasDerivAt.add h1.hasDerivAt h2.hasDerivAt).deriv
    have e2 : deriv (fun τ => deriv f τ * g τ) τ = deriv (deriv f) τ * g τ + deriv f τ * deriv g τ :=
      (HasDerivAt.mul (hf.differentiable_deriv τ).hasDerivAt (hg.differentiable τ).hasDerivAt).deriv
    have e3 : deriv (fun τ => f τ * deriv g τ) τ = deriv f τ * deriv g τ + f τ * deriv (deriv g) τ :=
      (HasDerivAt.mul (hf.differentiable τ).hasDerivAt (hg.differentiable_deriv τ).hasDerivAt).deriv
    rw [e, e2, e3]
    ring
  refine ⟨ContDiff.mul hf.1 hg.1, fun τ => ⟨?_, ?_, ?_⟩⟩
  · rw [norm_mul]
    have := mul_le_mul (hf.2 τ).1 (hg.2 τ).1 (norm_nonneg _) (hP τ)
    nlinarith [mul_nonneg (hP τ) (hQ τ)]
  · rw [hd1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have a1 := mul_le_mul (hf.2 τ).2.1 (hg.2 τ).1 (norm_nonneg _) (hP τ)
    have a2 := mul_le_mul (hf.2 τ).1 (hg.2 τ).2.1 (norm_nonneg _) (hP τ)
    nlinarith [mul_nonneg (hP τ) (hQ τ)]
  · rw [hd2]
    refine (norm_add_le _ _).trans ((add_le_add_left (norm_add_le _ _) _).trans ?_)
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    simp only [norm_mul, h2]
    have a1 := mul_le_mul (hf.2 τ).2.2 (hg.2 τ).1 (norm_nonneg _) (hP τ)
    have a2 := mul_le_mul (hf.2 τ).2.1 (hg.2 τ).2.1 (norm_nonneg _) (hP τ)
    have a3 := mul_le_mul (hf.2 τ).1 (hg.2 τ).2.2 (norm_nonneg _) (hP τ)
    nlinarith [mul_nonneg (hP τ) (hQ τ)]

lemma Env2.const {c : ℂ} : Env2 (fun _ : ℝ => c) (fun _ => ‖c‖) := by
  refine ⟨contDiff_const, fun τ => ?_⟩
  simp

lemma Env2.const_mul {f : ℝ → ℂ} {P : ℝ → ℝ} (h : Env2 f P) (c : ℂ) :
    Env2 (fun τ => c * f τ) (fun τ => 4 * ‖c‖ * P τ) :=
  Env2.const.mul h


lemma Env2.add {f g : ℝ → ℂ} {P Q : ℝ → ℝ} (hf : Env2 f P) (hg : Env2 g Q) :
    Env2 (fun τ => f τ + g τ) (fun τ => P τ + Q τ) := by
  have hd1 : deriv (fun τ => f τ + g τ) = fun τ => deriv f τ + deriv g τ := by
    funext τ; exact (HasDerivAt.add (hf.differentiable τ).hasDerivAt (hg.differentiable τ).hasDerivAt).deriv
  have hd2 : deriv (deriv (fun τ => f τ + g τ)) = fun τ => deriv (deriv f) τ + deriv (deriv g) τ := by
    rw [hd1]; funext τ
    exact (HasDerivAt.add (hf.differentiable_deriv τ).hasDerivAt (hg.differentiable_deriv τ).hasDerivAt).deriv
  refine ⟨ContDiff.add hf.1 hg.1, fun τ => ⟨?_, ?_, ?_⟩⟩
  · exact (norm_add_le _ _).trans (add_le_add (hf.2 τ).1 (hg.2 τ).1)
  · rw [hd1]; exact (norm_add_le _ _).trans (add_le_add (hf.2 τ).2.1 (hg.2 τ).2.1)
  · rw [hd2]; exact (norm_add_le _ _).trans (add_le_add (hf.2 τ).2.2 (hg.2 τ).2.2)

lemma Env2.ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (P : ℝ → ℝ) (h0 : ∀ τ, |f τ| ≤ P τ)
    (h1 : ∀ τ, |deriv f τ| ≤ P τ) (h2 : ∀ τ, |deriv (deriv f) τ| ≤ P τ) :
    Env2 (fun τ => (f τ : ℂ)) P := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h2' : ContDiff ℝ ((1 : ℕ) + 1) f := by simpa [one_add_one_eq_two] using hf
  have hdf1 : Differentiable ℝ (deriv f) :=
    (((contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2').2.2).differentiable (by norm_num)
  have hd1 : deriv (fun τ => (f τ : ℂ)) = fun τ => ((deriv f τ : ℝ) : ℂ) := by
    funext τ; exact (hdf τ).hasDerivAt.ofReal_comp.deriv
  have hd2 : deriv (deriv (fun τ => (f τ : ℂ))) = fun τ => ((deriv (deriv f) τ : ℝ) : ℂ) := by
    rw [hd1]; funext τ; exact (hdf1 τ).hasDerivAt.ofReal_comp.deriv
  refine ⟨Complex.ofRealCLM.contDiff.comp hf, fun τ => ⟨?_, ?_, ?_⟩⟩
  · simpa using h0 τ
  · rw [hd1]; simpa using h1 τ
  · rw [hd2]; simpa using h2 τ

lemma Env2.exp_neg {G : ℝ → ℂ} {P : ℝ → ℝ} (hG : Env2 G P) (b : ℝ → ℝ)
    (hb : ∀ τ, ‖Complex.exp (-G τ)‖ ≤ b τ) :
    Env2 (fun τ => Complex.exp (-G τ)) (fun τ => b τ * (1 + 2 * P τ + P τ ^ 2)) := by
  have hP : ∀ τ, 0 ≤ P τ := fun τ => (norm_nonneg _).trans (hG.2 τ).1
  have hbn : ∀ τ, 0 ≤ b τ := fun τ => (norm_nonneg _).trans (hb τ)
  have hd1 : deriv (fun τ => Complex.exp (-G τ)) = fun τ => -deriv G τ * Complex.exp (-G τ) := by
    funext τ
    have := ((hG.differentiable τ).hasDerivAt.neg).cexp
    exact this.deriv.trans (by simp only [Pi.neg_apply]; ring)
  have hE1 : ∀ τ, DifferentiableAt ℝ (fun τ => Complex.exp (-G τ)) τ := fun τ =>
    (((hG.differentiable τ).hasDerivAt.neg).cexp).differentiableAt
  have hd2 : deriv (deriv (fun τ => Complex.exp (-G τ))) =
      fun τ => (deriv G τ ^ 2 - deriv (deriv G) τ) * Complex.exp (-G τ) := by
    rw [hd1]; funext τ
    have h1 : HasDerivAt (fun τ => -deriv G τ) (-deriv (deriv G) τ) τ := (hG.differentiable_deriv τ).hasDerivAt.neg
    have h2 := h1.mul ((hG.differentiable τ).hasDerivAt.neg).cexp
    exact h2.deriv.trans (by simp only [Pi.neg_apply]; ring)
  have hcd : ContDiff ℝ 2 (fun τ => Complex.exp (-G τ)) := ContDiff.cexp hG.1.neg
  refine ⟨hcd, fun τ => ⟨?_, ?_, ?_⟩⟩
  all_goals show _ ≤ b τ * (1 + 2 * P τ + P τ ^ 2)
  · have := (hb τ)
    nlinarith [mul_nonneg (hbn τ) (hP τ), mul_nonneg (hbn τ) (sq_nonneg (P τ)), hbn τ]
  · rw [hd1, norm_mul, norm_neg]
    have a1 := mul_le_mul (hG.2 τ).2.1 (hb τ) (norm_nonneg _) (hP τ)
    nlinarith [mul_nonneg (hbn τ) (hP τ), mul_nonneg (hbn τ) (sq_nonneg (P τ)), hbn τ]
  · rw [hd2, norm_mul]
    have c1 : ‖deriv G τ ^ 2 - deriv (deriv G) τ‖ ≤ P τ ^ 2 + P τ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow]
      have := (hG.2 τ).2.1
      have := (hG.2 τ).2.2
      have h3 : ‖deriv G τ‖ ^ 2 ≤ P τ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hG.2 τ).2.1 2
      linarith
    have a1 := mul_le_mul c1 (hb τ) (norm_nonneg _) (by nlinarith [hP τ, sq_nonneg (P τ)])
    nlinarith [mul_nonneg (hbn τ) (hP τ), mul_nonneg (hbn τ) (sq_nonneg (P τ)), hbn τ]

/-- info: 'FormalResearch.SignUncertainty.Env2.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Env2.mul

/-- info: 'FormalResearch.SignUncertainty.Env2.exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Env2.exp_neg

end FormalResearch.SignUncertainty
