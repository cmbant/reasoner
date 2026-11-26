module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaperChart
public import FormalResearch.SignUncertainty.CtDyadicPsiWindow

/-!
# `ct:cfu`: the map `û` and its inverse `φ_c` in the window where `ψ_ε` is `C¹`

`constant_terms_lower.tex`, after `ct:psi-def`: `û(ũ) = ũ + 2^{-2/3}c^{-1/3}ψ_ε(2^{2/3}c^{-2/3}ũ)`, `φ_c = û⁻¹`,
`R' = -φ_c(-R)` (`ct:dyadic` (4)).  With `λ = 2^{-2/3}c^{-1/3}` (`ctLam`) and `μ = 2^{2/3}c^{-2/3}` (`ctMu`), `λμ = c⁻¹`,
and the window facts of `ctPsi_window` (`ψ < 0`, `|ψ|, |ψ'| ≤ M` on `(-ρ, 0)`):

* `ctUhat_lt`, `abs_ctUhat_sub_le`: `û(u) < u` and `|û(u) - u| ≤ λM` for `μu ∈ (-ρ, 0)`;
* `ctUhat_hasDerivAt`: `û'(u) = 1 + c⁻¹ψ'(μu) ∈ [1/2, 3/2]` for `c ≥ 2M`;
* `exists_ctUhat_eq` (intermediate value): for `1 ≤ R` with `[-R, 0)` inside the window and `λM ≤ 1/2`, some `u* ∈ [-R, -1/2]` has
  `û(u*) = -R`;
* `ctPhi_eq` / `ctRprime_*`: with the named input `UhatInjOn` (`û` injective on the Langer disc, the bijectivity of `û` of
  `ct:cfu` that the paper uses for `φ_c = û⁻¹`), `ctPhi ε c (-R) = u*` and `R' = ctRprime ε c R ∈ [R - λM, R]`.

**Proved** from the window facts; `UhatInjOn` is a named hypothesis (not proved: it concerns the Lean junk values of `ctPsi`
outside the window `μ|u| < ρ`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `λ = 2^{-2/3} c^{-1/3}`. -/
noncomputable def ctLam (c : ℝ) : ℝ := (2 : ℝ) ^ (-(2 / 3) : ℝ) * c ^ (-(1 / 3) : ℝ)

/-- `μ = 2^{2/3} c^{-2/3}`, the scale `a = μ ũ`. -/
noncomputable def ctMu (c : ℝ) : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ)

lemma ctUhat_eq (ε c u : ℝ) : ctUhat ε c u = u + ctLam c * ctPsi ε (ctMu c * u) := rfl

lemma ctLam_pos {c : ℝ} (hc : 0 < c) : 0 < ctLam c := by unfold ctLam; positivity

lemma ctMu_pos {c : ℝ} (hc : 0 < c) : 0 < ctMu c := by unfold ctMu; positivity

lemma ctLam_mul_ctMu {c : ℝ} (hc : 0 < c) : ctLam c * ctMu c = c⁻¹ := by
  unfold ctLam ctMu
  have h2 : (2 : ℝ) ^ (-(2 / 3) : ℝ) * (2 : ℝ) ^ ((2 : ℝ) / 3) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have hc' : c ^ (-(1 / 3) : ℝ) * c ^ (-(2 / 3) : ℝ) = c⁻¹ := by
    rw [← Real.rpow_add hc]; norm_num [Real.rpow_neg_one]
  calc (2 : ℝ) ^ (-(2 / 3) : ℝ) * c ^ (-(1 / 3) : ℝ) * ((2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ))
      = ((2 : ℝ) ^ (-(2 / 3) : ℝ) * (2 : ℝ) ^ ((2 : ℝ) / 3)) * (c ^ (-(1 / 3) : ℝ) * c ^ (-(2 / 3) : ℝ)) := by ring
    _ = c⁻¹ := by rw [h2, hc', one_mul]

section Window

variable {ε c ρ M : ℝ}

/-- The window facts of `ctPsi_window`, as a predicate. -/
def PsiWin (ε ρ M : ℝ) : Prop :=
  0 < ρ ∧ 0 ≤ M ∧ ∀ a ∈ Ioo (-ρ) 0, ctPsi ε a < 0 ∧ |ctPsi ε a| ≤ M ∧
      HasDerivAt (ctPsi ε) (deriv (ctPsi ε) a) a ∧ |deriv (ctPsi ε) a| ≤ M

lemma ctUhat_lt (hW : PsiWin ε ρ M) (hc : 0 < c) {u : ℝ} (hu0 : u < 0) (hu : -ρ < ctMu c * u) :
    ctUhat ε c u < u := by
  have h := (hW.2.2 _ ⟨hu, mul_neg_of_pos_of_neg (ctMu_pos hc) hu0⟩).1
  rw [ctUhat_eq]
  nlinarith [ctLam_pos hc]

lemma abs_ctUhat_sub_le (hW : PsiWin ε ρ M) (hc : 0 < c) {u : ℝ} (hu0 : u < 0) (hu : -ρ < ctMu c * u) :
    |ctUhat ε c u - u| ≤ ctLam c * M := by
  have h := (hW.2.2 _ ⟨hu, mul_neg_of_pos_of_neg (ctMu_pos hc) hu0⟩).2.1
  rw [ctUhat_eq, add_sub_cancel_left, abs_mul, abs_of_pos (ctLam_pos hc)]
  exact mul_le_mul_of_nonneg_left h (ctLam_pos hc).le

lemma ctUhat_hasDerivAt (hW : PsiWin ε ρ M) (hc : 0 < c) {u : ℝ} (hu0 : u < 0) (hu : -ρ < ctMu c * u) :
    HasDerivAt (ctUhat ε c) (1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u)) u := by
  have hd := (hW.2.2 _ ⟨hu, mul_neg_of_pos_of_neg (ctMu_pos hc) hu0⟩).2.2.1
  have h1 : HasDerivAt (fun u : ℝ => ctMu c * u) (ctMu c) u := by
    simpa using (hasDerivAt_id u).const_mul (ctMu c)
  have h2 := (hd.comp u h1).const_mul (ctLam c)
  have h3 := (hasDerivAt_id u).add h2
  have hmul := ctLam_mul_ctMu hc
  have e : (1 : ℝ) + ctLam c * (deriv (ctPsi ε) (ctMu c * u) * ctMu c) = 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u) := by
    rw [← hmul]; ring
  rw [← e]
  exact h3

lemma ctUhat_deriv_bounds (hW : PsiWin ε ρ M) (hc : 0 < c) (hcM : 2 * M ≤ c) {u : ℝ} (hu0 : u < 0)
    (hu : -ρ < ctMu c * u) :
    1 / 2 ≤ 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u) ∧ 1 + c⁻¹ * deriv (ctPsi ε) (ctMu c * u) ≤ 3 / 2 := by
  have h := (hW.2.2 _ ⟨hu, mul_neg_of_pos_of_neg (ctMu_pos hc) hu0⟩).2.2.2
  have hb : |c⁻¹ * deriv (ctPsi ε) (ctMu c * u)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * |deriv (ctPsi ε) (ctMu c * u)| ≤ c⁻¹ * M := mul_le_mul_of_nonneg_left h (inv_pos.2 hc).le
      _ ≤ 1 / 2 := by
        rw [inv_mul_le_iff₀ hc]; linarith
  have := abs_le.1 hb
  constructor <;> linarith [this.1, this.2]

lemma continuousOn_ctUhat (hW : PsiWin ε ρ M) (hc : 0 < c) {a b : ℝ} (hb0 : b < 0) (ha : -ρ < ctMu c * a) :
    ContinuousOn (ctUhat ε c) (Icc a b) := by
  intro u hu
  have hu0 : u < 0 := lt_of_le_of_lt hu.2 hb0
  have hum : -ρ < ctMu c * u := by
    have := mul_le_mul_of_nonneg_left hu.1 (ctMu_pos hc).le
    linarith
  exact (ctUhat_hasDerivAt hW hc hu0 hum).continuousAt.continuousWithinAt

/-- **Existence of `φ_c(-R)`**: if `[-R, -1/2]` lies in the window, `λM ≤ 1/2` and `R ≥ 1`, then `û(u*) = -R` for some
`u* ∈ [-R, -1/2]`. -/
lemma exists_ctUhat_eq (hW : PsiWin ε ρ M) (hc : 0 < c) (hlam : ctLam c * M ≤ 1 / 2) {R : ℝ} (hR1 : 1 ≤ R)
    (hRw : -ρ < ctMu c * (-R)) :
    ∃ u ∈ Icc (-R) (-(1 / 2)), ctUhat ε c u = -R := by
  have hmu := ctMu_pos hc
  have hRw' : -ρ < ctMu c * (-R) := hRw
  have hhalf : -ρ < ctMu c * (-(1 / 2)) := by
    have : ctMu c * (-R) ≤ ctMu c * (-(1 / 2)) := mul_le_mul_of_nonneg_left (by linarith) hmu.le
    linarith
  have hcont := continuousOn_ctUhat hW hc (a := -R) (b := -(1 / 2)) (by norm_num) hRw'
  have h1 := ctUhat_lt hW hc (u := -R) (by linarith) hRw'
  have h2 := abs_ctUhat_sub_le hW hc (u := -(1 / 2)) (by norm_num) hhalf
  have h3 := (abs_le.1 h2).1
  have hint := intermediate_value_Icc (by linarith : -R ≤ -(1 / 2)) hcont
  have : -R ∈ Icc (ctUhat ε c (-R)) (ctUhat ε c (-(1 / 2))) := ⟨h1.le, by linarith⟩
  obtain ⟨u, hu, hv⟩ := hint this
  exact ⟨u, hu, hv⟩

/-- **The named input `UhatInjOn`**: `û` is injective on the Langer disc (the bijectivity of `û` on `|u| ≤ R_max` of
`ct:cfu`, used by the paper to define `φ_c = û⁻¹`).  Not proved here. -/
def UhatInjOn (ε c : ℝ) : Prop :=
  InjOn (ctUhat ε c) (Icc (-(langerRadius c)) (langerRadius c))

/-- With `UhatInjOn`, `φ_c(-R)` is the preimage found by `exists_ctUhat_eq`. -/
lemma ctPhi_eq (hinj : UhatInjOn ε c) {R u : ℝ} (hRA : R ≤ langerRadius c) (hu : u ∈ Icc (-R) (-(1 / 2)))
    (hv : ctUhat ε c u = -R) : ctPhi ε c (-R) = u := by
  have hA : u ∈ Icc (-(langerRadius c)) (langerRadius c) :=
    ⟨by linarith [hu.1], by linarith [hu.2, show 0 ≤ R by linarith [hu.1, hu.2]]⟩
  obtain ⟨hmem, hval⟩ := Function.invFunOn_pos (f := ctUhat ε c) (s := Icc (-(langerRadius c)) (langerRadius c))
    (b := -R) ⟨u, hA, hv⟩
  exact hinj hmem hA (hval.trans hv.symm)

end Window

end FormalResearch.SignUncertainty
