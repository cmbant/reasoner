/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctNPiece

/-!
# `hN` of Lemma FCT.7b: the `φ_kill` factor `|1 - L₁ φ_kill(iτ₀(L̃); a)/L̃| - 1` is a symbol of class `(M, -1, 0)`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`) (a), fourth item, with
`fct:phikill` (1) (`a = c^{-1/12}`, `t = τ₀(L̃)`) and `|L₁| ≤ C c^{-2/3} = C a⁸` (`fct:warp-asymp` (1)).

Write `‖L̃ - L₁Φ‖/L̃ = √(1 + w)` with `w = -2p + p² + q²`, `p = L₁ Re Φ/L̃`, `q = L₁ Im Φ/L̃`; `p, q` are symbols of class `(M, -1, 0)`
(`pieceN_usym`) and `|w| ≤ 1/2` as soon as `|L₁| ≤ η δ`, `η` absolute.  The composition with `G(y) = √(1 + y) - 1` is `SymW.comp_smooth`.

* `N_symW_abstract`: for `|L₁| ≤ κ a⁸`, `|L₁| ≤ η δ`, `|s| ≤ 3δ/4`, `3δ/2 ≤ 1/2`: the factor is in
  `SymW [3δ/2, ∞) (pw M (-1) 0) K` with `M = M(κ)`, `K = K(κ)` independent of `a, δ, s, L₁`.

Class: proved, no hypotheses.
-/

@[expose] public section

open Set Filter Topology Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open FormalResearch.SignUncertainty FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter
  FormalResearch.SignUncertainty.FctPhiKill

lemma USym.comap {Q P : Type*} {H : P → Prop} {S : P → Set ℝ} {w f : P → ℝ → ℝ} (h : USym H S w f) (φ : Q → P)
    {H' : Q → Prop} (hH : ∀ q, H' q → H (φ q)) :
    USym H' (fun q => S (φ q)) (fun q => w (φ q)) (fun q => f (φ q)) := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun q hq => hK (φ q) (hH q hq)⟩

lemma pw_smul (c M α β x : ℝ) : c * pw M α β x = pw (c * M) α β x := by
  unfold pw; ring

/-! ### The square root `G(y) = √(1 + y) - 1` -/

/-- `G(y) = √(1 + y) - 1`. -/
noncomputable def sqrtG (y : ℝ) : ℝ := Real.sqrt (1 + y) - 1

lemma contDiffOn_sqrtG : ContDiffOn ℝ ∞ sqrtG (Ioi (-1)) := by
  unfold sqrtG
  refine ContDiffOn.sub ((contDiffOn_const.add contDiffOn_id).sqrt fun y hy => ?_) contDiffOn_const
  have : -1 < y := hy
  simp only [id]; linarith

lemma abs_sqrtG_le {y : ℝ} (hy : -1 ≤ y) : |sqrtG y| ≤ |y| := by
  unfold sqrtG
  set r := Real.sqrt (1 + y) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r * r = 1 + y := Real.mul_self_sqrt (by linarith)
  have h1 : y = (r - 1) * (r + 1) := by nlinarith
  have h2 : |y| = |r - 1| * (r + 1) := by
    rw [h1, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < r + 1)]
  rw [h2]
  nlinarith [abs_nonneg (r - 1)]

lemma sqrtG_bounds (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc (-(1 / 2) : ℝ) (1 / 2), |iteratedDeriv j sqrtG y| ≤ B := by
  obtain ⟨B, hB⟩ := CtMDeriv.bdd_iter_on_compact (isOpen_Ioi (a := (-1 : ℝ))) contDiffOn_sqrtG
    (isCompact_Icc (a := -(1 / 2 : ℝ)) (b := 1 / 2)) (fun y hy => by
      show -1 < y
      linarith [hy.1]) j
  exact ⟨|B|, abs_nonneg _, fun y hy => (hB y hy).trans (le_abs_self _)⟩


lemma norm_sub_div_eq {u L₁ : ℝ} (hu : 0 < u) (Ψ : ℂ) :
    ‖(u : ℂ) - (L₁ : ℂ) * Ψ‖ / u - 1 =
      sqrtG (-2 * (L₁ * Ψ.re / u) + (L₁ * Ψ.re / u) * (L₁ * Ψ.re / u) + (L₁ * Ψ.im / u) * (L₁ * Ψ.im / u)) := by
  unfold sqrtG
  have h1 : 1 + (-2 * (L₁ * Ψ.re / u) + (L₁ * Ψ.re / u) * (L₁ * Ψ.re / u) + (L₁ * Ψ.im / u) * (L₁ * Ψ.im / u)) =
      (‖(u : ℂ) - (L₁ : ℂ) * Ψ‖ / u) ^ 2 := by
    rw [div_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    field_simp
    ring
  rw [h1, Real.sqrt_sq (div_nonneg (norm_nonneg _) hu.le)]

lemma phiKill_norm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a t : ℝ), 0 < a → ‖phiKill a ((t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ : ∃ C ≥ (0 : ℝ), ∀ {a : ℝ} {z : ℂ}, 0 < a → 0 ≤ z.re →
      ‖phiKill a z‖ ≤ C * min ((‖z‖ / a) ^ 8) 1 := (fct_phikill).2.2.2.2.2.1
  refine ⟨C₁, hC₁0, fun a t ha => (hC₁ ha (by simp)).trans ?_⟩
  have := min_le_right ((‖(t : ℂ) * Complex.I‖ / a) ^ 8) 1
  nlinarith


/-- **`hN` abstractly** (see the module docstring): the `φ_kill` factor of Lemma FCT.7b is a symbol of class `(M, -1, 0)` on `[3δ/2, ∞)`,
with `M, K` independent of `a, δ, s, L₁` (they depend on the bound `|L₁| ≤ κ a⁸` only). -/
theorem N_symW_abstract : ∃ η : ℝ, 0 < η ∧ ∀ κ : ℝ, 0 ≤ κ → ∃ (M : ℝ) (K : ℕ → ℝ), 0 ≤ M ∧
    ∀ a δ s L₁ : ℝ, 0 < a → a ≤ 1 → 0 < δ → 3 / 2 * δ ≤ 1 / 2 → |s| ≤ 3 / 4 * δ → |L₁| ≤ κ * a ^ 8 →
      |L₁| ≤ η * δ →
    SymW (Ici (3 / 2 * δ)) (pw M (-1) 0) K
      (fun x => ‖((x - s : ℝ) : ℂ) - (L₁ : ℂ) * phiKill a ((tau0 (x - s) : ℂ) * Complex.I)‖ / (x - s) - 1) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := phiKill_norm_le
  have hη : 0 < 1 / (40 * (C₁ + 1)) := by positivity
  refine ⟨1 / (40 * (C₁ + 1)), hη, fun κ hκ => ?_⟩
  obtain ⟨M, hM0, hpc⟩ := pieceN_usym κ hκ
  set η : ℝ := 1 / (40 * (C₁ + 1)) with hηdef
  -- the parameter predicate
  set H : NPar → Prop := fun q => 0 < q.a ∧ q.a ≤ 1 ∧ 0 < q.x₀ ∧ q.x₀ ≤ 1 / 2 ∧ |q.s| ≤ q.x₀ / 2 ∧
    |q.L₁| ≤ κ * q.a ^ 8 ∧ |q.L₁| ≤ η * (2 / 3 * q.x₀) with hH
  have hHre : ∀ q, H q → NHyp { q with L := Complex.reCLM } ∧ |q.L₁| ≤ κ * q.a ^ 8 := fun q hq =>
    ⟨⟨fun z => Complex.abs_re_le_norm z, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1⟩, hq.2.2.2.2.2.1⟩
  have hHim : ∀ q, H q → NHyp { q with L := Complex.imCLM } ∧ |q.L₁| ≤ κ * q.a ^ 8 := fun q hq =>
    ⟨⟨fun z => Complex.abs_im_le_norm z, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1⟩, hq.2.2.2.2.2.1⟩
  have p₁ := hpc.comap (fun q : NPar => { q with L := Complex.reCLM }) hHre
  have p₂ := hpc.comap (fun q : NPar => { q with L := Complex.imCLM }) hHim
  set M' : ℝ := 2 * M + 2 * (M * M) with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have t1 := (p₁.smul (fun _ => (-2 : ℝ))).of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le hq.2.2.1 hx
    show |(-2 : ℝ)| * pw M (-1) 0 x ≤ pw M' (-1) 0 x
    rw [show |(-2 : ℝ)| = 2 by norm_num, pw_smul]
    exact pw_le_pw (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) (by positivity) le_rfl le_rfl hx0)
  have t2 := (p₁.mul p₁).of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le hq.2.2.1 hx
    show pw M (-1) 0 x * pw M (-1) 0 x ≤ pw M' (-1) 0 x
    rw [pw_mul _ _ _ _ _ _ x hx0]
    exact pw_le_pw (M := M * M) (M' := M') (α := -1 + -1) (α' := -1) (β := 0 + 0) (β' := 0)
      (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) (mul_nonneg hM0 hM0) (by norm_num) (by norm_num) hx0)
  have t3 := (p₂.mul p₂).of_le (w' := fun _ => pw M' (-1) 0) (fun q hq x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le hq.2.2.1 hx
    show pw M (-1) 0 x * pw M (-1) 0 x ≤ pw M' (-1) 0 x
    rw [pw_mul _ _ _ _ _ _ x hx0]
    exact pw_le_pw (M := M * M) (M' := M') (α := -1 + -1) (α' := -1) (β := 0 + 0) (β' := 0)
      (by rw [hM']; nlinarith [mul_nonneg hM0 hM0]) (mul_nonneg hM0 hM0) (by norm_num) (by norm_num) hx0)
  have wsum := (t1.add t2).add t3
  -- smallness of the pieces
  have hpq : ∀ q : NPar, H q → ∀ x ∈ Ici q.x₀, ∀ L : ℂ →L[ℝ] ℝ, (∀ z, |L z| ≤ ‖z‖) →
      |q.L₁ * L (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)| ≤ 1 / 30 := by
    intro q hq x hx L hL
    have hx' : q.x₀ ≤ x := hx
    have hu : q.x₀ / 2 ≤ x - q.s := by linarith [(abs_le.mp hq.2.2.2.2.1).2]
    have hu0 : 0 < x - q.s := lt_of_lt_of_le (by linarith [hq.2.2.1]) hu
    rw [abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
    have h1 : |L (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I))| ≤ C₁ :=
      (hL _).trans (hC₁ q.a (tau0 (x - q.s)) hq.1)
    have h2 := hq.2.2.2.2.2.2
    have hη' : η * (C₁ + 1) = 1 / 40 := by rw [hηdef]; field_simp
    have hx0 := hq.2.2.1
    calc |q.L₁| * |L (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I))|
        ≤ (η * (2 / 3 * q.x₀)) * C₁ := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
      _ ≤ 1 / 30 * (x - q.s) := by
          have hx0 := hq.2.2.1
          nlinarith [mul_pos hη hx0, mul_nonneg hη.le hC₁0, mul_nonneg (mul_nonneg hη.le hC₁0) hx0.le]
  have hw_small : ∀ q : NPar, H q → ∀ x ∈ Ici q.x₀,
      |-2 * (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) +
        (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) *
          (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) +
        (q.L₁ * Complex.imCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) *
          (q.L₁ * Complex.imCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s))| ≤ 1 / 2 := by
    intro q hq x hx
    have hp := hpq q hq x hx Complex.reCLM (fun z => Complex.abs_re_le_norm z)
    have hq' := hpq q hq x hx Complex.imCLM (fun z => Complex.abs_im_le_norm z)
    set P := q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)
    set Q := q.L₁ * Complex.imCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)
    have hP := abs_le.mp hp
    have hQ := abs_le.mp hq'
    rw [abs_le]
    constructor <;> nlinarith [hP.1, hP.2, hQ.1, hQ.2, sq_nonneg P, sq_nonneg Q]
  obtain ⟨Kw, hKw⟩ := wsum
  choose Bj hBj0 hBj using sqrtG_bounds
  have wsum' : USym H (fun q => Ici q.x₀) (fun _ => pw M' (-1) 0) (fun q x =>
      -2 * (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) +
        (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) *
          (q.L₁ * Complex.reCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) +
        (q.L₁ * Complex.imCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s)) *
          (q.L₁ * Complex.imCLM (phiKill q.a ((tau0 (x - q.s) : ℂ) * Complex.I)) / (x - q.s))) :=
    ⟨Kw, fun q hq => hKw q hq⟩
  have hcomp := wsum'.comp_smooth (Φ := sqrtG) (V := Ioi (-1)) (Pj := Bj) (B := M') (L := max (Kw 0) 0)
    isOpen_Ioi contDiffOn_sqrtG
    (fun q hq x hx => by
      have := abs_le.mp (hw_small q hq x hx)
      show -1 < _
      linarith [this.1])
    (fun q hq j x hx => hBj j _ (by
      have := abs_le.mp (hw_small q hq x hx)
      exact ⟨this.1, this.2⟩))
    (fun j => hBj0 j)
    (fun q hq x hx => pw_const_le hM'0 (by norm_num) le_rfl (lt_of_lt_of_le hq.2.2.1 hx))
    (le_max_right _ _)
    (fun q hq x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hq.2.2.1 hx
      have hw := abs_le.mp (hw_small q hq x hx)
      refine (abs_sqrtG_le (by linarith [hw.1])).trans ?_
      have h2 := (hKw q hq).bound 0 x hx
      simp only [pow_zero, inv_one, mul_one] at h2
      refine h2.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pw_nonneg hM'0 hx0))
  obtain ⟨K, hK⟩ := hcomp
  refine ⟨M', K, hM'0, fun a δ s L₁ ha ha1 hδ hδ1 hs hL1 hη2 => ?_⟩
  have hq : H ⟨Complex.reCLM, a, s, 3 / 2 * δ, L₁⟩ := by
    refine ⟨ha, ha1, by linarith, hδ1, ?_, hL1, ?_⟩
    · show |s| ≤ 3 / 2 * δ / 2
      linarith
    · show |L₁| ≤ η * (2 / 3 * (3 / 2 * δ))
      rw [show 2 / 3 * (3 / 2 * δ) = δ by ring]; exact hη2
  refine (hK _ hq).congr (U := Ioi δ) isOpen_Ioi (fun x hx => ?_) (fun x hx => ?_)
  · have : 3 / 2 * δ ≤ x := hx
    exact lt_of_lt_of_le (by linarith) this
  · have hxδ : δ < x := hx
    have hu : 0 < x - s := by linarith [(abs_le.mp hs).2]
    simp only
    rw [norm_sub_div_eq hu]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply]

/-- info: 'FormalResearch.SignUncertainty.FctSym.N_symW_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms N_symW_abstract

end FormalResearch.SignUncertainty.FctSym
