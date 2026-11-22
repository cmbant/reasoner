module

public import FormalResearch.Special.AiryClarkLabel
public import FormalResearch.Special.AiryCftQNCUnc
public import FormalResearch.Special.AiryCft2FirstDerivZero
public import FormalResearch.Special.AiryCftSignUncertainty
public import FormalResearch.Special.AiryCftSignEqualityDiv
public import FormalResearch.Special.AiryCftSignEqualityMain
public import FormalResearch.Special.AiryThm47Liouville
public import FormalResearch.Special.AiryThm47Div
public import FormalResearch.Special.AiryThm47Poly
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryFirstZeros


/-!
# Clark Two-Node Sign Uncertainty (`clark_airy.tex`, Theorem 1.2)

For `α ∈ (-π/2, π/2] \ {0}` (`sin α ≠ 0`), let `ψ_α(u) = cos α · Ai(u) - sin α · Ai'(u)`
(`psiClark α`) with top zeros `z₁(α) > z₂(α)` (`clarkNode α 1`, `clarkNode α 2`) and extremal
`g_α(u) = ψ_α(u)² / ((u - z₁(α))(u - z₂(α)))` (`clarkExtremal α`).

* `clarkNode_one_bijOn`, `existsUnique_clarkAngle_of_gt`: `α ↦ z₁(α)` bijects `(-π/2, π/2] \ {0}` onto `(a₁, ∞)`.
* `clarkExtremal_attains`: `g_α ∈ 𝒢_{-3/2} ⊂ 𝒢`, `∫ g_α = 0`, `g_α ≢ 0`, sign changes at `z₂(α), z₁(α)`.
* `clark_two_node_uncertainty`, `clark_two_node_equality_iff`, `clark_two_node_of_gt_firstZero`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Part 1: Clark angle parameterisation, `ψ_α`, and top nodes -/

/-- The Clark parameter domain `(-π/2, π/2] \ {0}`. -/
def clarkAngleDomain : Set ℝ := Set.Ioc (-(π / 2)) (π / 2) \ {0}

/-- Every `α ∈ (-π/2, π/2] \ {0}` satisfies `sin α ≠ 0`. -/
lemma sin_ne_zero_of_mem_clarkAngleDomain {α : ℝ} (hα : α ∈ clarkAngleDomain) : Real.sin α ≠ 0 := by
  rcases hα with ⟨⟨h1, h2⟩, hne⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact (Real.sin_neg_of_neg_of_neg_pi_lt hneg (by linarith [Real.pi_pos])).ne
  · exact (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith [Real.pi_pos])).ne'

/-- The complex Clark function `ψ_α(u) = cos α · Ai(u) - sin α · Ai'(u)`. -/
noncomputable def psiClark (α : ℝ) (u : ℂ) : ℂ :=
  (Real.cos α : ℂ) * airyAiC u - (Real.sin α : ℂ) * deriv airyAiC u

/-- `ψ_α` coincides with `airyNC (cos α) (-sin α)`. -/
lemma psiClark_eq_airyNC (α : ℝ) (u : ℂ) :
    psiClark α u = airyNC (Real.cos α) (-Real.sin α) u := by
  unfold psiClark airyNC
  push_cast
  ring

lemma differentiable_psiClark (α : ℝ) : Differentiable ℂ (psiClark α) := by
  have : psiClark α = airyNC (Real.cos α) (-Real.sin α) := funext (psiClark_eq_airyNC α)
  rw [this]
  exact differentiable_airyNC _ _

lemma psiClark_ofReal (α x : ℝ) :
    psiClark α (x : ℂ) = ((SturmAiry.combo α airyAi airyAi' x : ℝ) : ℂ) := by
  unfold psiClark SturmAiry.combo
  rw [airyAiC_ofReal, deriv_airyAiC_ofReal]
  push_cast
  ring

/-- The `n`-th Clark node `z_n(α)` (`n ≥ 1`, decreasing in `n`: `z_1(α) > a_1 > z_2(α) > a_2 > …`). -/
noncomputable def clarkNode (α : ℝ) (n : ℕ) : ℝ := airyClarkAngleNode α n

/-- `α ↦ z_1(α)` is a bijection of `(-π/2, π/2] \ {0}` onto `(a_1, ∞)`. -/
theorem clarkNode_one_bijOn :
    Set.BijOn (fun α : ℝ => clarkNode α 1) clarkAngleDomain (Set.Ioi (airyZero 1)) := by
  have hbij := airyClarkAngleNode_bijOn (n := 1) le_rfl
  rw [airyClarkGap_one] at hbij
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    rcases hα with ⟨⟨h1, h2⟩, hne⟩
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hmem : α + π ∈ Set.Ioo 0 π := ⟨by linarith, by linarith⟩
      simpa [clarkNode, airyClarkAngleNode_add_pi] using hbij.mapsTo hmem
    · have hmem : α ∈ Set.Ioo 0 π := ⟨hpos, by linarith [Real.pi_pos]⟩
      exact hbij.mapsTo hmem
  · intro α₁ h₁ α₂ h₂ heq
    let φ : ℝ → ℝ := fun α => if 0 < α then α else α + π
    have hφ_mem : ∀ α ∈ clarkAngleDomain, φ α ∈ Set.Ioo 0 π := by
      intro α hα
      rcases hα with ⟨⟨h1, h2⟩, hne⟩
      dsimp only [φ]
      split_ifs with hpos
      · exact ⟨hpos, by linarith [Real.pi_pos]⟩
      · have hneg : α < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
        exact ⟨by linarith, by linarith⟩
    have hφ_node : ∀ α, clarkNode (φ α) 1 = clarkNode α 1 := by
      intro α
      dsimp only [φ]
      split_ifs
      · rfl
      · exact airyClarkAngleNode_add_pi α 1
    have hφ_eq : φ α₁ = φ α₂ := by
      refine hbij.injOn (hφ_mem α₁ h₁) (hφ_mem α₂ h₂) ?_
      change clarkNode (φ α₁) 1 = clarkNode (φ α₂) 1
      rw [hφ_node, hφ_node]
      exact heq
    rcases h₁ with ⟨⟨h11, h12⟩, h1ne⟩
    rcases h₂ with ⟨⟨h21, h22⟩, h2ne⟩
    dsimp only [φ] at hφ_eq
    split_ifs at hφ_eq with p1 p2
    · exact hφ_eq
    · exfalso; linarith
    · exfalso; linarith
    · linarith
  · intro u hu
    obtain ⟨β, hβ, rfl⟩ := hbij.surjOn hu
    by_cases hle : β ≤ π / 2
    · refine ⟨β, ⟨⟨by linarith [hβ.1, Real.pi_pos], hle⟩, hβ.1.ne'⟩, rfl⟩
    · have hgt : π / 2 < β := not_le.mp hle
      refine ⟨β - π, ⟨⟨by linarith, by linarith [hβ.2, Real.pi_pos]⟩, ne_of_lt (by linarith [hβ.2])⟩, ?_⟩
      change airyClarkAngleNode (β - π) 1 = airyClarkAngleNode β 1
      simpa [sub_add_cancel] using (airyClarkAngleNode_add_pi (β - π) 1).symm

/-- Every `u₁ > a₁` determines a unique `α ∈ (-π/2, π/2] \ {0}` with `z₁(α) = u₁`. -/
theorem existsUnique_clarkAngle_of_gt {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) :
    ∃! α : ℝ, α ∈ clarkAngleDomain ∧ clarkNode α 1 = u₁ := by
  obtain ⟨α, hα, hval⟩ := clarkNode_one_bijOn.surjOn hu₁
  exact ⟨α, ⟨hα, hval⟩, fun β ⟨hβ, hβval⟩ => clarkNode_one_bijOn.injOn hβ hα (hβval.trans hval.symm)⟩

lemma clarkNode_lt_of_lt {n m : ℕ} (hn : 1 ≤ n) (h : n < m) (α : ℝ) :
    clarkNode α m < clarkNode α n := by
  induction m, h using Nat.le_induction with
  | base =>
    have hsucc := airyClarkNode_succ_lt hn (Real.cos α / Real.sin α)
    exact hsucc.1.trans hsucc.2
  | succ m hm ih =>
    have hsucc := airyClarkNode_succ_lt (by omega : 1 ≤ m) (Real.cos α / Real.sin α)
    exact (hsucc.1.trans hsucc.2).trans ih

lemma clarkNode_two_lt_one (α : ℝ) : clarkNode α 2 < clarkNode α 1 :=
  clarkNode_lt_of_lt le_rfl (by norm_num) α

lemma clarkNode_zero {α : ℝ} (hα : Real.sin α ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    psiClark α (clarkNode α n : ℂ) = 0 := by
  rw [psiClark_ofReal, Complex.ofReal_eq_zero, airyClarkAngle_zero_iff hα]
  exact ⟨n, hn, rfl⟩

lemma clarkNode_deriv_ne_zero {α : ℝ} (hα : Real.sin α ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    deriv (psiClark α) (clarkNode α n : ℂ) ≠ 0 := by
  have hfn : psiClark α = airyNC (Real.cos α) (-Real.sin α) := funext (psiClark_eq_airyNC α)
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hz : airyNC (Real.cos α) (-Real.sin α) (clarkNode α n : ℂ) = 0 := by
    rw [← psiClark_eq_airyNC]
    exact clarkNode_zero hα hn
  rw [hfn, deriv_airyNC]
  exact (airyNC_zero_weight_pos (Real.cos α) (-Real.sin α) hQ hz).2

lemma psiClark_zero_iff {α : ℝ} (hα : Real.sin α ≠ 0) (z : ℂ) :
    psiClark α z = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ z = (clarkNode α n : ℂ) := by
  constructor
  · intro h
    have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
    rw [psiClark_eq_airyNC] at h
    have him := airyNC_zero_im (Real.cos α) (-Real.sin α) hQ h
    have ez : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [ez, ← psiClark_eq_airyNC, psiClark_ofReal, Complex.ofReal_eq_zero,
      airyClarkAngle_zero_iff hα] at h
    obtain ⟨n, hn, hxn⟩ := h
    exact ⟨n, hn, by rw [ez, hxn]; rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact clarkNode_zero hα hn

/-! ### Part 1.2: The Clark two-node extremal `g_α` -/

/-- The entire Clark two-node extremal `g_α(u) = ψ_α(u)² / ((u - z₁(α))(u - z₂(α)))`
(defined via `dslope` so `Differentiable ℂ` holds everywhere without removable-singularity patching). -/
noncomputable def clarkExtremal (α : ℝ) (u : ℂ) : ℂ :=
  dslope (psiClark α) (clarkNode α 1 : ℂ) u * dslope (psiClark α) (clarkNode α 2 : ℂ) u

theorem differentiable_clarkExtremal (α : ℝ) : Differentiable ℂ (clarkExtremal α) := by
  unfold clarkExtremal
  exact (EntireDiv.differentiable_dslope_entire (differentiable_psiClark α) _).mul
    (EntireDiv.differentiable_dslope_entire (differentiable_psiClark α) _)

lemma clarkExtremal_mul_denom {α : ℝ} (hα : Real.sin α ≠ 0) (u : ℂ) :
    clarkExtremal α u * ((u - (clarkNode α 1 : ℂ)) * (u - (clarkNode α 2 : ℂ))) =
      psiClark α u ^ 2 := by
  have e1 : (u - (clarkNode α 1 : ℂ)) • dslope (psiClark α) (clarkNode α 1 : ℂ) u =
      psiClark α u - psiClark α (clarkNode α 1 : ℂ) :=
    sub_smul_dslope (psiClark α) (clarkNode α 1 : ℂ) u
  have e2 : (u - (clarkNode α 2 : ℂ)) • dslope (psiClark α) (clarkNode α 2 : ℂ) u =
      psiClark α u - psiClark α (clarkNode α 2 : ℂ) :=
    sub_smul_dslope (psiClark α) (clarkNode α 2 : ℂ) u
  rw [smul_eq_mul, clarkNode_zero hα le_rfl, sub_zero] at e1
  rw [smul_eq_mul, clarkNode_zero hα (by norm_num), sub_zero] at e2
  unfold clarkExtremal
  calc dslope (psiClark α) (clarkNode α 1 : ℂ) u * dslope (psiClark α) (clarkNode α 2 : ℂ) u *
        ((u - (clarkNode α 1 : ℂ)) * (u - (clarkNode α 2 : ℂ)))
      = ((u - (clarkNode α 1 : ℂ)) * dslope (psiClark α) (clarkNode α 1 : ℂ) u) *
          ((u - (clarkNode α 2 : ℂ)) * dslope (psiClark α) (clarkNode α 2 : ℂ) u) := by ring
    _ = psiClark α u * psiClark α u := by rw [e1, e2]
    _ = psiClark α u ^ 2 := by ring

lemma clarkExtremal_eq {α : ℝ} (hα : Real.sin α ≠ 0) {u : ℂ}
    (h1 : u ≠ (clarkNode α 1 : ℂ)) (h2 : u ≠ (clarkNode α 2 : ℂ)) :
    clarkExtremal α u =
      psiClark α u ^ 2 / ((u - (clarkNode α 1 : ℂ)) * (u - (clarkNode α 2 : ℂ))) := by
  have hden : (u - (clarkNode α 1 : ℂ)) * (u - (clarkNode α 2 : ℂ)) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)
  rw [eq_div_iff hden]
  exact clarkExtremal_mul_denom hα u

lemma clarkExtremal_at_one {α : ℝ} (hα : Real.sin α ≠ 0) :
    clarkExtremal α (clarkNode α 1 : ℂ) = 0 := by
  have hne : (clarkNode α 1 : ℂ) ≠ (clarkNode α 2 : ℂ) := by
    intro h
    have := Complex.ofReal_injective h
    linarith [clarkNode_two_lt_one α]
  unfold clarkExtremal
  rw [dslope_of_ne _ hne, slope_def_field, clarkNode_zero hα le_rfl, clarkNode_zero hα (by norm_num)]
  simp

lemma clarkExtremal_at_two {α : ℝ} (hα : Real.sin α ≠ 0) :
    clarkExtremal α (clarkNode α 2 : ℂ) = 0 := by
  have hne : (clarkNode α 2 : ℂ) ≠ (clarkNode α 1 : ℂ) := by
    intro h
    have := Complex.ofReal_injective h
    linarith [clarkNode_two_lt_one α]
  unfold clarkExtremal
  rw [dslope_of_ne _ hne, slope_def_field, clarkNode_zero hα (by norm_num), clarkNode_zero hα le_rfl]
  simp

lemma clarkExtremal_ofReal {α : ℝ} (hα : Real.sin α ≠ 0) (x : ℝ) :
    (clarkExtremal α (x : ℂ)).im = 0 := by
  by_cases h1 : x = clarkNode α 1
  · rw [h1, clarkExtremal_at_one hα]; simp
  · by_cases h2 : x = clarkNode α 2
    · rw [h2, clarkExtremal_at_two hα]; simp
    · have h1c : (x : ℂ) ≠ (clarkNode α 1 : ℂ) := fun h => h1 (Complex.ofReal_injective h)
      have h2c : (x : ℂ) ≠ (clarkNode α 2 : ℂ) := fun h => h2 (Complex.ofReal_injective h)
      rw [clarkExtremal_eq hα h1c h2c, psiClark_ofReal]
      have e : (((SturmAiry.combo α airyAi airyAi' x : ℝ) : ℂ) ^ 2 /
            (((x : ℂ) - (clarkNode α 1 : ℂ)) * ((x : ℂ) - (clarkNode α 2 : ℂ)))) =
          (((SturmAiry.combo α airyAi airyAi' x ^ 2 /
            ((x - clarkNode α 1) * (x - clarkNode α 2)) : ℝ)) : ℂ) := by
        push_cast; rfl
      rw [e, Complex.ofReal_im]

lemma clarkExtremal_re {α : ℝ} (hα : Real.sin α ≠ 0) {x : ℝ}
    (h1 : x ≠ clarkNode α 1) (h2 : x ≠ clarkNode α 2) :
    (clarkExtremal α (x : ℂ)).re =
      SturmAiry.combo α airyAi airyAi' x ^ 2 / ((x - clarkNode α 1) * (x - clarkNode α 2)) := by
  have h1c : (x : ℂ) ≠ (clarkNode α 1 : ℂ) := fun h => h1 (Complex.ofReal_injective h)
  have h2c : (x : ℂ) ≠ (clarkNode α 2 : ℂ) := fun h => h2 (Complex.ofReal_injective h)
  rw [clarkExtremal_eq hα h1c h2c, psiClark_ofReal]
  have e : (((SturmAiry.combo α airyAi airyAi' x : ℝ) : ℂ) ^ 2 /
        (((x : ℂ) - (clarkNode α 1 : ℂ)) * ((x : ℂ) - (clarkNode α 2 : ℂ)))) =
      (((SturmAiry.combo α airyAi airyAi' x ^ 2 /
        ((x - clarkNode α 1) * (x - clarkNode α 2)) : ℝ)) : ℂ) := by
    push_cast; rfl
  rw [e, Complex.ofReal_re]

lemma psiClark_real_ne_zero_of_gt_two {α : ℝ} (hα : Real.sin α ≠ 0) {x : ℝ}
    (hx2 : clarkNode α 2 < x) (hx1 : x ≠ clarkNode α 1) :
    SturmAiry.combo α airyAi airyAi' x ≠ 0 := by
  intro h0
  rw [airyClarkAngle_zero_iff hα] at h0
  obtain ⟨n, hn, rfl⟩ := h0
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have : n = 1 := by omega
    subst this; exact hx1 rfl
  · rcases hge.eq_or_lt with rfl | hgt
    · change clarkNode α 2 < clarkNode α 2 at hx2
      linarith
    · have hlt := clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) hgt α
      change clarkNode α 2 < clarkNode α n at hx2
      linarith

lemma clarkExtremal_nonneg_band {α : ℝ} (hα : Real.sin α ≠ 0) {x : ℝ} (hx : x ≤ clarkNode α 2) :
    0 ≤ (clarkExtremal α (x : ℂ)).re := by
  rcases hx.eq_or_lt with rfl | hlt
  · rw [clarkExtremal_at_two hα]; simp
  · have hlt1 : x < clarkNode α 1 := hlt.trans (clarkNode_two_lt_one α)
    rw [clarkExtremal_re hα hlt1.ne hlt.ne]
    have hden : 0 < (x - clarkNode α 1) * (x - clarkNode α 2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    exact div_nonneg (sq_nonneg _) hden.le

lemma clarkExtremal_neg_between {α : ℝ} (hα : Real.sin α ≠ 0) {x : ℝ}
    (hx2 : clarkNode α 2 < x) (hx1 : x < clarkNode α 1) :
    (clarkExtremal α (x : ℂ)).re < 0 := by
  rw [clarkExtremal_re hα hx1.ne hx2.ne']
  have hψ := psiClark_real_ne_zero_of_gt_two hα hx2 hx1.ne
  have hnum : 0 < SturmAiry.combo α airyAi airyAi' x ^ 2 := sq_pos_of_ne_zero hψ
  have hden : (x - clarkNode α 1) * (x - clarkNode α 2) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  exact div_neg_of_pos_of_neg hnum hden

lemma clarkExtremal_pos_above {α : ℝ} (hα : Real.sin α ≠ 0) {x : ℝ} (hx1 : clarkNode α 1 < x) :
    0 < (clarkExtremal α (x : ℂ)).re := by
  have hx2 : clarkNode α 2 < x := (clarkNode_two_lt_one α).trans hx1
  rw [clarkExtremal_re hα hx1.ne' hx2.ne']
  have hψ := psiClark_real_ne_zero_of_gt_two hα hx2 hx1.ne'
  have hnum : 0 < SturmAiry.combo α airyAi airyAi' x ^ 2 := sq_pos_of_ne_zero hψ
  have hden : 0 < (x - clarkNode α 1) * (x - clarkNode α 2) :=
    mul_pos (by linarith) (by linarith)
  exact div_pos hnum hden

lemma clarkExtremal_pos_at_airyZero_two {α : ℝ} (hα : Real.sin α ≠ 0) :
    0 < (clarkExtremal α (airyZero 2 : ℂ)).re := by
  have h2lt : airyZero 2 < clarkNode α 2 := airyZero_lt_airyClarkNode (by norm_num) _
  have h1lt : airyZero 2 < clarkNode α 1 := h2lt.trans (clarkNode_two_lt_one α)
  rw [clarkExtremal_re hα h1lt.ne h2lt.ne]
  have hψ : SturmAiry.combo α airyAi airyAi' (airyZero 2) ≠ 0 := by
    unfold SturmAiry.combo
    rw [airyAi_airyZero, mul_zero, zero_sub]
    have hd : airyAi' (airyZero 2) ≠ 0 := by
      have := airyZero_deriv_ne_zero 2
      rw [deriv_airyAiC_ofReal] at this
      intro h0
      apply this
      rw [h0]; simp
    exact neg_ne_zero.mpr (mul_ne_zero hα hd)
  have hden : 0 < (airyZero 2 - clarkNode α 1) * (airyZero 2 - clarkNode α 2) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  exact div_pos (sq_pos_of_ne_zero hψ) hden

lemma clarkExtremal_ne_zero {α : ℝ} (hα : Real.sin α ≠ 0) :
    ∃ z : ℂ, clarkExtremal α z ≠ 0 := by
  refine ⟨((clarkNode α 1 + 1 : ℝ) : ℂ), fun h => ?_⟩
  have hp := clarkExtremal_pos_above hα (x := clarkNode α 1 + 1) (by linarith)
  rw [h] at hp
  simp at hp

/-- Squared complex envelope of `ψ_α`: `‖ψ_α(u)‖² ≤ 64 (1 + ‖u‖)^{1/2} e(u)`. -/
lemma psiClark_norm_sq_le (α : ℝ) (u : ℂ) :
    ‖psiClark α u‖ ^ 2 ≤ 64 * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u := by
  have hx1 : 1 ≤ 1 + ‖u‖ := by linarith [norm_nonneg u]
  have h1 := airyAiC_envelope u
  have h2 := airyAiC_deriv_envelope u
  have hp : (1 + ‖u‖) ^ (-(1 / 4) : ℝ) ≤ (1 + ‖u‖) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have he : 0 ≤ Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re) := (Real.exp_pos _).le
  have hA : ‖airyAiC u‖ ≤ 3 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re) :=
    h1.trans (by gcongr)
  have hc : ‖(Real.cos α : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one α
  have hs : ‖(Real.sin α : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_sin_le_one α
  have hψ : ‖psiClark α u‖ ≤
      8 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re) := by
    unfold psiClark
    calc ‖(Real.cos α : ℂ) * airyAiC u - (Real.sin α : ℂ) * deriv airyAiC u‖
        ≤ ‖(Real.cos α : ℂ) * airyAiC u‖ + ‖(Real.sin α : ℂ) * deriv airyAiC u‖ := norm_sub_le _ _
      _ = ‖(Real.cos α : ℂ)‖ * ‖airyAiC u‖ + ‖(Real.sin α : ℂ)‖ * ‖deriv airyAiC u‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * (3 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) +
            1 * (5 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) := by
          gcongr
      _ = _ := by ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hψ 2
  refine hsq.trans (le_of_eq ?_)
  have e1 : ((1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 = (1 + ‖u‖) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2 = airyEnv u := by
    rw [airyEnv, ← Real.exp_nat_mul]; norm_num; ring_nf
  calc (8 * (1 + ‖u‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2
      = 64 * ((1 + ‖u‖) ^ (1 / 4 : ℝ)) ^ 2 * (Real.exp (-(2 / 3) * (u ^ (3 / 2 : ℂ)).re)) ^ 2 := by
        ring
    _ = _ := by rw [e1, e2]

lemma norm_sub_ofReal_ge {t : ℝ} {u : ℂ} (hu : |t| + 1 ≤ ‖u‖) :
    1 + ‖u‖ ≤ (2 + |t|) * ‖u - (t : ℂ)‖ ∧ u ≠ (t : ℂ) := by
  have ht : ‖(t : ℂ)‖ = |t| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 : 1 ≤ ‖u - (t : ℂ)‖ := by
    have := norm_sub_norm_le u (t : ℂ)
    rw [ht] at this
    linarith
  have hne : u ≠ (t : ℂ) := fun h => by rw [h, sub_self, norm_zero] at h1; linarith
  have h2 : ‖u‖ ≤ ‖u - (t : ℂ)‖ + |t| := by
    have := norm_add_le (u - (t : ℂ)) (t : ℂ)
    rw [sub_add_cancel, ht] at this
    exact this
  refine ⟨?_, hne⟩
  nlinarith [abs_nonneg t]

/-- **`g_α ∈ 𝒢_{-3/2} ⊂ 𝒢`**: `‖g_α(u)‖ ≤ C (1 + ‖u‖)^{-3/2} e(u)` on `ℂ`. -/
theorem clarkExtremal_bound {α : ℝ} (hα : Real.sin α ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖clarkExtremal α u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by
  set z₁ := clarkNode α 1 with hz₁
  set z₂ := clarkNode α 2 with hz₂
  set B : ℝ := |z₁| + |z₂| + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) B).exists_bound_of_continuousOn
    (differentiable_clarkExtremal α).continuous.continuousOn
  set e0 : ℝ := Real.exp (-(4 / 3) * B ^ (3 / 2 : ℝ)) with he0
  set m1 : ℝ := min 1 ((1 + B) ^ (-(3 / 2) : ℝ)) with hm1
  have he0p : 0 < e0 := Real.exp_pos _
  have hm1p : 0 < m1 := lt_min one_pos (Real.rpow_pos_of_pos (by linarith) _)
  set C₀ : ℝ := 64 * (2 + |z₁|) * (2 + |z₂|) with hC₀
  refine ⟨max C₀ (|M| / (m1 * e0)), by positivity, fun u => ?_⟩
  by_cases hu : ‖u‖ ≤ B
  · have h1 : ‖clarkExtremal α u‖ ≤ |M| := (hM u (by simpa using hu)).trans (le_abs_self _)
    have h2 : m1 * e0 ≤ (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u :=
      mul_le_mul (at47_rpow_lower hu) (at47_env_lower hu hB0) he0p.le
        (Real.rpow_nonneg (by linarith [norm_nonneg u]) _)
    have h3 : |M| ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    calc ‖clarkExtremal α u‖ ≤ |M| / (m1 * e0) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) :=
          h1.trans h3
      _ ≤ max C₀ (|M| / (m1 * e0)) * ((1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (mul_nonneg (Real.rpow_nonneg (by positivity) _) (airyEnv_pos u).le)
      _ = _ := by ring
  · replace hu := not_le.mp hu
    obtain ⟨hg1, hne1⟩ := norm_sub_ofReal_ge (t := z₁) (u := u) (by linarith [abs_nonneg z₂])
    obtain ⟨hg2, hne2⟩ := norm_sub_ofReal_ge (t := z₂) (u := u) (by linarith [abs_nonneg z₁])
    rw [clarkExtremal_eq hα hne1 hne2, norm_div, norm_mul, norm_pow]
    have hψ := psiClark_norm_sq_le α u
    have he_pos : 0 ≤ airyEnv u := (airyEnv_pos u).le
    have hx : 0 < 1 + ‖u‖ := by positivity
    have hden1 : 0 < ‖u - (z₁ : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne1)
    have hden2 : 0 < ‖u - (z₂ : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne2)
    have hmul : (1 + ‖u‖) ^ 2 ≤ ((2 + |z₁|) * (2 + |z₂|)) * (‖u - (z₁ : ℂ)‖ * ‖u - (z₂ : ℂ)‖) := by
      calc (1 + ‖u‖) ^ 2 = (1 + ‖u‖) * (1 + ‖u‖) := by ring
        _ ≤ ((2 + |z₁|) * ‖u - (z₁ : ℂ)‖) * ((2 + |z₂|) * ‖u - (z₂ : ℂ)‖) :=
            mul_le_mul hg1 hg2 hx.le (by positivity)
        _ = _ := by ring
    have hinv : (‖u - (z₁ : ℂ)‖ * ‖u - (z₂ : ℂ)‖)⁻¹ ≤
        ((2 + |z₁|) * (2 + |z₂|)) * (1 + ‖u‖) ^ (-2 : ℝ) := by
      have hpow2 : (1 + ‖u‖) ^ (-2 : ℝ) = ((1 + ‖u‖) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hpow2, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hpow : (1 + ‖u‖) ^ (1 / 2 : ℝ) * (1 + ‖u‖) ^ (-2 : ℝ) = (1 + ‖u‖) ^ (-(3 / 2) : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    calc ‖psiClark α u‖ ^ 2 / (‖u - (z₁ : ℂ)‖ * ‖u - (z₂ : ℂ)‖)
        = ‖psiClark α u‖ ^ 2 * (‖u - (z₁ : ℂ)‖ * ‖u - (z₂ : ℂ)‖)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (64 * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u) *
            (((2 + |z₁|) * (2 + |z₂|)) * (1 + ‖u‖) ^ (-2 : ℝ)) :=
          mul_le_mul hψ hinv (by positivity) (by positivity)
      _ = C₀ * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by
          rw [hC₀, ← hpow]; ring
      _ ≤ max C₀ (|M| / (m1 * e0)) * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _)) he_pos

theorem clarkExtremal_integrable {α : ℝ} (hα : Real.sin α ≠ 0) :
    Integrable (fun x : ℝ => clarkExtremal α (x : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := clarkExtremal_bound hα
  exact airy_integrable_real (differentiable_clarkExtremal α) hC (by norm_num) hb

theorem clarkExtremal_integral {α : ℝ} (hα : Real.sin α ≠ 0) :
    (∫ x : ℝ, clarkExtremal α (x : ℂ)) = 0 := by
  obtain ⟨C, hC, hb⟩ := clarkExtremal_bound hα
  have hsum := airyClark_hasSum_unc α hα (differentiable_clarkExtremal α)
    (clarkExtremal_integrable hα) hC hb
  have hzero : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      clarkExtremal α z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2) = 0 := by
    intro z
    have hψ : psiClark α z.1 = 0 := z.2
    obtain ⟨n, hn, hzn⟩ := (psiClark_zero_iff hα z.1).1 hψ
    have hgz : clarkExtremal α z.1 = 0 := by
      rcases eq_or_ne n 1 with rfl | hn1
      · rw [hzn]; exact clarkExtremal_at_one hα
      · rcases eq_or_ne n 2 with rfl | hn2
        · rw [hzn]; exact clarkExtremal_at_two hα
        · have h1c : z.1 ≠ (clarkNode α 1 : ℂ) := by
            rw [hzn]
            intro h; exact hn1 (by
              have := Complex.ofReal_injective h
              have := clarkNode_lt_of_lt le_rfl (by omega : 1 < n) α
              linarith)
          have h2c : z.1 ≠ (clarkNode α 2 : ℂ) := by
            rw [hzn]
            intro h; exact hn2 (by
              have := Complex.ofReal_injective h
              have := clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) (by omega : 2 < n) α
              linarith)
          rw [clarkExtremal_eq hα h1c h2c, hψ]
          simp
    rw [hgz, zero_div]
  simp_rw [hzero] at hsum
  exact hsum.unique hasSum_zero

/-- **Sharpness of Theorem 1.2**: `g_α` is entire, integrable on `ℝ`, in `𝒢_{-3/2} ⊂ 𝒢`, real on `ℝ`,
vanishes at `z₁(α)` and `z₂(α)`, is `≥ 0` on `(-∞, z₂(α)]`, `< 0` on `(z₂(α), z₁(α))`, `> 0` on `(z₁(α), ∞)`,
has `∫_ℝ g_α = 0`, and `g_α ≢ 0`. -/
theorem clarkExtremal_attains {α : ℝ} (hα : Real.sin α ≠ 0) :
    Differentiable ℂ (clarkExtremal α) ∧
      Integrable (fun x : ℝ => clarkExtremal α (x : ℂ)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖clarkExtremal α u‖ ≤ C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) ∧
      (∀ x : ℝ, (clarkExtremal α (x : ℂ)).im = 0) ∧
      clarkExtremal α (clarkNode α 1 : ℂ) = 0 ∧
      clarkExtremal α (clarkNode α 2 : ℂ) = 0 ∧
      (∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (clarkExtremal α (x : ℂ)).re) ∧
      (∀ x : ℝ, clarkNode α 2 < x → x < clarkNode α 1 → (clarkExtremal α (x : ℂ)).re < 0) ∧
      (∀ x : ℝ, clarkNode α 1 < x → 0 < (clarkExtremal α (x : ℂ)).re) ∧
      (∫ x : ℝ, (clarkExtremal α (x : ℂ)).re) = 0 ∧
      (∃ z : ℂ, clarkExtremal α z ≠ 0) := by
  refine ⟨differentiable_clarkExtremal α, clarkExtremal_integrable hα, clarkExtremal_bound hα,
    clarkExtremal_ofReal hα, clarkExtremal_at_one hα, clarkExtremal_at_two hα,
    fun x hx => clarkExtremal_nonneg_band hα hx,
    fun x hx2 hx1 => clarkExtremal_neg_between hα hx2 hx1,
    fun x hx1 => clarkExtremal_pos_above hα hx1,
    ?_, clarkExtremal_ne_zero hα⟩
  have hint_re : (∫ x : ℝ, (clarkExtremal α (x : ℂ)).re) = (∫ x : ℝ, clarkExtremal α (x : ℂ)).re := by
    simpa using integral_re (clarkExtremal_integrable hα)
  rw [hint_re, clarkExtremal_integral hα]
  simp

/-- info: 'FormalResearch.SignUncertainty.clarkNode_one_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkNode_one_bijOn

/-- info: 'FormalResearch.SignUncertainty.existsUnique_clarkAngle_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.existsUnique_clarkAngle_of_gt

/-- info: 'FormalResearch.SignUncertainty.clarkExtremal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkExtremal_bound

/-- info: 'FormalResearch.SignUncertainty.clarkExtremal_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkExtremal_integrable

/-- info: 'FormalResearch.SignUncertainty.clarkExtremal_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkExtremal_integral

/-- info: 'FormalResearch.SignUncertainty.clarkExtremal_attains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clarkExtremal_attains

/-! ### Part 1.3: Two-node sign uncertainty and equality case -/

/-- Exact integration-by-parts antiderivative for `ψ_α(x)² - (sin² α / 2) K(x,x)` on `ℝ`:
`W(x) = -cos²α K(x,x) + (sin²α / 2) Ai(x)Ai'(x) - cos α sin α Ai(x)²`. -/
private noncomputable def clarkBandW (α x : ℝ) : ℝ :=
  -(Real.cos α ^ 2) * airyKer x x + (Real.sin α ^ 2 / 2) * (airyAi x * airyAi' x) -
    Real.cos α * Real.sin α * airyAi x ^ 2

private lemma hasDerivAt_clarkBandW (α x : ℝ) :
    HasDerivAt (clarkBandW α)
      (SturmAiry.combo α airyAi airyAi' x ^ 2 - (Real.sin α ^ 2 / 2) * airyKer x x) x := by
  have hK := hasDerivAt_airyKer_diag x
  have hA := hasDerivAt_airyAi x
  have hB := hasDerivAt_airyAi' x
  have h1 := hK.const_mul (-(Real.cos α ^ 2))
  have h2 := (hA.mul hB).const_mul (Real.sin α ^ 2 / 2)
  have h3 := (hA.pow 2).const_mul (Real.cos α * Real.sin α)
  have h := (h1.add h2).sub h3
  refine h.congr_deriv ?_
  unfold SturmAiry.combo
  rw [airyKer_self]
  ring

private lemma clarkBandW_abs_le (α : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    |clarkBandW α (-y)| ≤ 26 * √y := by
  have hy0 : 0 < y := by linarith
  have hsq : 1 ≤ √y := by rw [Real.one_le_sqrt]; exact hy
  have hK : airyKer (-y) (-y) ≤ 2 * √y := by
    have h := (abs_le.mp (airyKer_diag_neg hy)).2
    have hpi : π⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
    have h1 : √y / Real.pi ≤ √y := mul_le_of_le_one_right (Real.sqrt_nonneg _) hpi
    have h2 : 1 / y ≤ 1 := by rw [div_le_one hy0]; exact hy
    linarith
  have hK0 : 0 ≤ airyKer (-y) (-y) := airyKer_diag_nonneg (-y)
  have hA := abs_airyAi_le_of_nonpos (x := -y) (by linarith)
  have hB := abs_airyAi'_le_of_nonpos (x := -y) (by linarith)
  rw [abs_neg, abs_of_pos hy0] at hA hB
  have hp1 : 0 < 1 + y := by linarith
  have hAB : |airyAi (-y) * airyAi' (-y)| ≤ 15 := by
    rw [abs_mul]
    have hinv : (1 + y) ^ (-(1 / 4) : ℝ) * (1 + y) ^ (1 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hp1]; norm_num
    calc |airyAi (-y)| * |airyAi' (-y)|
        ≤ (3 * (1 + y) ^ (-(1 / 4) : ℝ)) * (5 * (1 + y) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 15 * ((1 + y) ^ (-(1 / 4) : ℝ) * (1 + y) ^ (1 / 4 : ℝ)) := by ring
      _ = 15 := by rw [hinv, mul_one]
  have hA2 : airyAi (-y) ^ 2 ≤ 9 := by
    have hq : (1 + y) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hA' : |airyAi (-y)| ≤ 3 := hA.trans (by nlinarith)
    rw [← sq_abs]
    nlinarith [abs_nonneg (airyAi (-y))]
  have hc : Real.cos α ^ 2 ≤ 1 := Real.cos_sq_le_one α
  have hs : Real.sin α ^ 2 ≤ 1 := Real.sin_sq_le_one α
  have hcs : |Real.cos α * Real.sin α| ≤ 1 := by
    calc |Real.cos α * Real.sin α| = |Real.cos α| * |Real.sin α| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (Real.abs_cos_le_one α) (Real.abs_sin_le_one α) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have t1 : |-(Real.cos α ^ 2) * airyKer (-y) (-y)| ≤ 1 * (2 * √y) := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.cos α)), abs_of_nonneg hK0]
    exact mul_le_mul hc hK hK0 zero_le_one
  have t2 : |(Real.sin α ^ 2 / 2) * (airyAi (-y) * airyAi' (-y))| ≤ (1 / 2) * 15 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sin α ^ 2 / 2)]
    exact mul_le_mul (by linarith) hAB (abs_nonneg _) (by positivity)
  have t3 : |Real.cos α * Real.sin α * airyAi (-y) ^ 2| ≤ 1 * 9 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (airyAi (-y)))]
    exact mul_le_mul hcs hA2 (sq_nonneg _) zero_le_one
  unfold clarkBandW
  calc |-(Real.cos α ^ 2) * airyKer (-y) (-y) + (Real.sin α ^ 2 / 2) * (airyAi (-y) * airyAi' (-y)) -
        Real.cos α * Real.sin α * airyAi (-y) ^ 2|
      ≤ |-(Real.cos α ^ 2) * airyKer (-y) (-y)| + |(Real.sin α ^ 2 / 2) * (airyAi (-y) * airyAi' (-y))| +
          |Real.cos α * Real.sin α * airyAi (-y) ^ 2| := by
        refine (abs_sub _ _).trans ?_; gcongr; exact abs_add_le _ _
    _ ≤ 1 * (2 * √y) + (1 / 2) * 15 + 1 * 9 := by linarith
    _ ≤ 26 * √y := by nlinarith

private lemma clark_band_block_integral {α : ℝ} (hα : Real.sin α ≠ 0) :
    ∃ c R0 : ℝ, 0 < c ∧ 4 ≤ R0 ∧ ∀ R : ℝ, R0 ≤ R →
      c * (R * √R) ≤ ∫ x in (-(2 * R))..(-R), SturmAiry.combo α airyAi airyAi' x ^ 2 := by
  have hpi := Real.pi_pos
  have hs2 : 0 < Real.sin α ^ 2 := sq_pos_of_ne_zero hα
  set R0 : ℝ := max 4 (1248 * π / Real.sin α ^ 2) with hR0
  refine ⟨Real.sin α ^ 2 / (8 * π), R0, by positivity, le_max_left _ _, fun R hR => ?_⟩
  have hR4 : 4 ≤ R := (le_max_left _ _).trans hR
  have hRbig : 1248 * π / Real.sin α ^ 2 ≤ R := (le_max_right _ _).trans hR
  have h2R1 : 1 ≤ 2 * R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hab : -(2 * R) ≤ -R := by linarith
  have hd : ∀ x ∈ Set.uIcc (-(2 * R)) (-R), HasDerivAt (clarkBandW α)
      (SturmAiry.combo α airyAi airyAi' x ^ 2 - (Real.sin α ^ 2 / 2) * airyKer x x) x :=
    fun x _ => hasDerivAt_clarkBandW α x
  have hc : Continuous (fun x : ℝ =>
      SturmAiry.combo α airyAi airyAi' x ^ 2 - (Real.sin α ^ 2 / 2) * airyKer x x) := by
    unfold SturmAiry.combo
    have hK : Continuous (fun x : ℝ => airyKer x x) := by
      simp_rw [airyKer_self]
      exact (continuous_airyAi'.pow 2).sub (continuous_id.mul (continuous_airyAi.pow 2))
    have := continuous_airyAi; have := continuous_airyAi'
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  have hc1 : Continuous (fun x : ℝ => SturmAiry.combo α airyAi airyAi' x ^ 2) := by
    unfold SturmAiry.combo; have := continuous_airyAi; have := continuous_airyAi'; fun_prop
  have hc2 : Continuous (fun x : ℝ => (Real.sin α ^ 2 / 2) * airyKer x x) := by
    have hK : Continuous (fun x : ℝ => airyKer x x) := by
      simp_rw [airyKer_self]
      exact (continuous_airyAi'.pow 2).sub (continuous_id.mul (continuous_airyAi.pow 2))
    exact continuous_const.mul hK
  rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)] at hftc
  have hKlow : ∀ x ∈ Set.Icc (-(2 * R)) (-R), √R / (2 * π) ≤ airyKer x x := by
    intro x hx
    set y := -x
    have hy4 : 4 ≤ y := by linarith [hx.2]
    have hxy : x = -y := by ring
    rw [hxy]
    have h := (abs_le.mp (airyKer_diag_neg (by linarith : 1 ≤ y))).1
    have hsy : √R ≤ √y := Real.sqrt_le_sqrt (by linarith [hx.2])
    have hy2 : 2 ≤ √y := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hy4
    have hpi4 : π < 4 := Real.pi_lt_four
    have h1y : 1 / y ≤ √y / (2 * π) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      have : 2 * π < 2 * 4 := by linarith
      nlinarith
    have : √y / π - √y / (2 * π) = √y / (2 * π) := by field_simp; ring
    have : √y / (2 * π) ≤ airyKer (-y) (-y) := by linarith
    calc √R / (2 * π) ≤ √y / (2 * π) := by gcongr
      _ ≤ airyKer (-y) (-y) := this
  have hKint : R * (√R / (2 * π)) ≤ ∫ x in (-(2 * R))..(-R), airyKer x x := by
    have hcK : Continuous (fun x : ℝ => airyKer x x) := by
      simp_rw [airyKer_self]
      exact (continuous_airyAi'.pow 2).sub (continuous_id.mul (continuous_airyAi.pow 2))
    have hmono : (∫ _x in (-(2 * R))..(-R), (√R / (2 * π) : ℝ)) ≤
        ∫ x in (-(2 * R))..(-R), airyKer x x :=
      intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _)
        (hcK.intervalIntegrable _ _) hKlow
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
    convert hmono using 1
    ring
  have hW1 := clarkBandW_abs_le α hR1
  have hW2 := clarkBandW_abs_le α h2R1
  have hsqrt2 : √(2 * R) ≤ 2 * √R := by
    rw [Real.sqrt_mul (by norm_num)]
    have : √2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    gcongr
  have hWdiff : |clarkBandW α (-R) - clarkBandW α (-(2 * R))| ≤ 78 * √R := by
    calc |clarkBandW α (-R) - clarkBandW α (-(2 * R))|
        ≤ |clarkBandW α (-R)| + |clarkBandW α (-(2 * R))| := abs_sub _ _
      _ ≤ 26 * √R + 26 * √(2 * R) := by gcongr
      _ ≤ 26 * √R + 26 * (2 * √R) := by gcongr
      _ = 78 * √R := by ring
  have hWlower : -(78 * √R) ≤ clarkBandW α (-R) - clarkBandW α (-(2 * R)) :=
    (abs_le.mp hWdiff).1
  have hKmul : (Real.sin α ^ 2 / 2) * (R * (√R / (2 * π))) ≤
      ∫ x in (-(2 * R))..(-R), (Real.sin α ^ 2 / 2) * airyKer x x := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hKint (by positivity)
  have hbig : 78 * √R ≤ Real.sin α ^ 2 / (8 * π) * (R * √R) := by
    have h1 : 1248 * π ≤ Real.sin α ^ 2 * R := by
      rw [div_le_iff₀ hs2] at hRbig; linarith
    have h2 : 78 * (8 * π) ≤ Real.sin α ^ 2 * R := by linarith
    have hsr0 : 0 ≤ √R := Real.sqrt_nonneg R
    rw [show Real.sin α ^ 2 / (8 * π) * (R * √R) = (Real.sin α ^ 2 * R) * √R / (8 * π) by ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have heq : (Real.sin α ^ 2 / 2) * (R * (√R / (2 * π))) =
      2 * (Real.sin α ^ 2 / (8 * π) * (R * √R)) := by field_simp; ring
  linarith

private lemma clark_blocks_not_integrable {h : ℝ → ℝ} (hint : Integrable h) (hnn : ∀ x, 0 ≤ h x)
    {c R0 : ℝ} (hc : 0 < c) (hR0 : 0 < R0)
    (hblock : ∀ R : ℝ, R0 ≤ R → c ≤ ∫ x in (-(2 * R))..(-R), h x) : False := by
  have hF : ∀ k : ℕ, (k : ℝ) * c ≤ ∫ x in (-(R0 * 2 ^ k))..(-R0), h x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      have hRk : R0 ≤ R0 * 2 ^ k := by nlinarith
      have e : -(R0 * 2 ^ (k + 1)) = -(2 * (R0 * 2 ^ k)) := by ring
      have hb := hblock (R0 * 2 ^ k) hRk
      have hsplit : ∫ x in (-(R0 * 2 ^ (k + 1)))..(-R0), h x =
          (∫ x in (-(R0 * 2 ^ (k + 1)))..(-(R0 * 2 ^ k)), h x) +
            ∫ x in (-(R0 * 2 ^ k))..(-R0), h x := by
        rw [intervalIntegral.integral_add_adjacent_intervals] <;> exact hint.intervalIntegrable
      rw [hsplit, e]
      push_cast
      linarith
  have hbound : ∀ k : ℕ, ∫ x in (-(R0 * 2 ^ k))..(-R0), h x ≤ ∫ x, h x := by
    intro k
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hle : -(R0 * 2 ^ k) ≤ -R0 := by nlinarith
    rw [intervalIntegral.integral_of_le hle]
    exact setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  obtain ⟨k, hk⟩ := exists_nat_gt ((∫ x, h x) / c)
  have h1 := (hF k).trans (hbound k)
  rw [div_lt_iff₀ hc] at hk
  linarith

private lemma clark_poly_mul_not_integrable {α : ℝ} (hα : Real.sin α ≠ 0) (p : ℂ[X])
    (hp : 1 ≤ p.natDegree) :
    ¬ Integrable (fun x : ℝ => p.eval (x : ℂ) * clarkExtremal α (x : ℂ)) := by
  intro hint
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  obtain ⟨c1, S1, hc1, hS1, hpl⟩ := at47_cpoly_lower hp0
  obtain ⟨c2, R2, hc2, hR2, hblock⟩ := clark_band_block_integral hα
  set z₁ := clarkNode α 1 with hz₁
  set z₂ := clarkNode α 2 with hz₂
  set T : ℝ := |z₁| + |z₂| + 1 with hT
  have hT0 : 0 < T := by positivity
  let h : ℝ → ℝ := fun x => ‖p.eval (x : ℂ) * clarkExtremal α (x : ℂ)‖
  have hint' : Integrable h := hint.norm
  have hnn : ∀ x, 0 ≤ h x := fun x => norm_nonneg _
  set R0 : ℝ := max (max R2 S1) T with hR0
  refine clark_blocks_not_integrable hint' hnn (c := c1 * c2 / 9) (R0 := R0)
    (by positivity) (by positivity) ?_
  intro R hR
  have hRR2 : R2 ≤ R := ((le_max_left _ _).trans (le_max_left _ _)).trans hR
  have hRS1 : S1 ≤ R := ((le_max_right _ _).trans (le_max_left _ _)).trans hR
  have hRT : T ≤ R := (le_max_right _ _).trans hR
  have hR1 : 1 ≤ R := hS1.trans hRS1
  have hab : -(2 * R) ≤ -R := by linarith
  have hpt : ∀ x ∈ Set.Icc (-(2 * R)) (-R),
      (c1 / (9 * R)) * SturmAiry.combo α airyAi airyAi' x ^ 2 ≤ h x := by
    intro x hx
    have hxR : R ≤ -x := by linarith [hx.2]
    have hx2 : -x ≤ 2 * R := by linarith [hx.1]
    have hxneg : x < 0 := by linarith
    have hxn : ‖(x : ℂ)‖ = -x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hxneg]
    have hpl' : c1 * R ^ p.natDegree ≤ ‖p.eval (x : ℂ)‖ := by
      have := hpl (x : ℂ) (by rw [hxn]; linarith)
      rw [hxn] at this
      exact le_trans (by gcongr) this
    have hplR : c1 * R ≤ ‖p.eval (x : ℂ)‖ := by
      have : R ^ 1 ≤ R ^ p.natDegree := pow_le_pow_right₀ hR1 hp
      rw [pow_one] at this
      exact (mul_le_mul_of_nonneg_left this hc1.le).trans hpl'
    have hne1 : x ≠ z₁ := fun h => by
      have : |z₁| ≤ T - 1 := by linarith [abs_nonneg z₂]
      linarith [neg_abs_le z₁, h ▸ hx.2]
    have hne2 : x ≠ z₂ := fun h => by
      have : |z₂| ≤ T - 1 := by linarith [abs_nonneg z₁]
      linarith [neg_abs_le z₂, h ▸ hx.2]
    have h1c : (x : ℂ) ≠ (z₁ : ℂ) := fun h => hne1 (Complex.ofReal_injective h)
    have h2c : (x : ℂ) ≠ (z₂ : ℂ) := fun h => hne2 (Complex.ofReal_injective h)
    have hden1 : |x - z₁| ≤ 3 * R := by
      have := abs_sub x z₁
      rw [abs_of_neg hxneg] at this
      linarith [abs_nonneg z₂]
    have hden2 : |x - z₂| ≤ 3 * R := by
      have := abs_sub x z₂
      rw [abs_of_neg hxneg] at this
      linarith [abs_nonneg z₁]
    have hden : |x - z₁| * |x - z₂| ≤ 9 * R ^ 2 := by
      calc |x - z₁| * |x - z₂| ≤ (3 * R) * (3 * R) :=
            mul_le_mul hden1 hden2 (abs_nonneg _) (by positivity)
        _ = 9 * R ^ 2 := by ring
    have hdenpos : 0 < |x - z₁| * |x - z₂| :=
      mul_pos (abs_pos.mpr (sub_ne_zero.mpr hne1)) (abs_pos.mpr (sub_ne_zero.mpr hne2))
    have hgx : ‖clarkExtremal α (x : ℂ)‖ =
        SturmAiry.combo α airyAi airyAi' x ^ 2 / (|x - z₁| * |x - z₂|) := by
      rw [clarkExtremal_eq hα h1c h2c, norm_div, norm_mul, norm_pow, psiClark_ofReal,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    dsimp only [h]
    rw [norm_mul, hgx]
    calc (c1 / (9 * R)) * SturmAiry.combo α airyAi airyAi' x ^ 2
        = (c1 * R) * SturmAiry.combo α airyAi airyAi' x ^ 2 / (9 * R ^ 2) := by
          have : 0 < R := by linarith
          field_simp
      _ ≤ ‖p.eval (x : ℂ)‖ * (SturmAiry.combo α airyAi airyAi' x ^ 2 / (|x - z₁| * |x - z₂|)) := by
          rw [mul_div_assoc']
          exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hplR (sq_nonneg _))
            hdenpos hden
  have hcN : ContinuousOn (fun x => (c1 / (9 * R)) * SturmAiry.combo α airyAi airyAi' x ^ 2)
      (Set.Icc (-(2 * R)) (-R)) := by
    unfold SturmAiry.combo; have := continuous_airyAi; have := continuous_airyAi'; fun_prop
  have hmono := intervalIntegral.integral_mono_on hab (hcN.intervalIntegrable_of_Icc hab)
    hint'.intervalIntegrable hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hb := hblock R hRR2
  have hsr1 : 1 ≤ √R := by rw [Real.one_le_sqrt]; exact hR1
  have h1 : c1 * c2 / 9 ≤ (c1 / (9 * R)) * (c2 * (R * √R)) := by
    have hR0' : 0 < R := by linarith
    have e : (c1 / (9 * R)) * (c2 * (R * √R)) = (c1 * c2 / 9) * √R := by
      field_simp
    rw [e]
    have : 0 < c1 * c2 / 9 := by positivity
    nlinarith
  exact h1.trans (hmono.trans' (mul_le_mul_of_nonneg_left hb (by positivity)))

/-- Local minimum of a real entire function gives a zero derivative. -/
private lemma clark_deriv_eq_zero_of_min {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {x u : ℝ} (hxu : x < u)
    (hnn : ∀ y : ℝ, y ≤ u → 0 ≤ (f (y : ℂ)).re) (h0 : f (x : ℂ) = 0) :
    deriv f (x : ℂ) = 0 := by
  have hd : HasDerivAt f (deriv f (x : ℂ)) (x : ℂ) := (hf (x : ℂ)).hasDerivAt
  have hre : HasDerivAt (fun y : ℝ => (f (y : ℂ)).re) (deriv f (x : ℂ)).re x := hd.real_of_complex
  have hmin : IsLocalMin (fun y : ℝ => (f (y : ℂ)).re) x := by
    filter_upwards [Iio_mem_nhds hxu] with y hy
    rw [h0]; simpa using hnn y (le_of_lt hy)
  have hre0 := hmin.hasDerivAt_eq_zero hre
  have h1 : HasDerivAt (fun y : ℝ => f (y : ℂ)) (deriv f (x : ℂ)) x := hd.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ => (((f (y : ℂ)).re : ℝ) : ℂ)) (((deriv f (x : ℂ)).re : ℝ) : ℂ) x :=
    hre.ofReal_comp
  have h3 : (fun y : ℝ => (((f (y : ℂ)).re : ℝ) : ℂ)) = fun y : ℝ => f (y : ℂ) :=
    funext fun y => (airy_real_cast hreal y).symm
  rw [h3] at h2
  have him0 : (deriv f (x : ℂ)).im = 0 := by
    have := h1.unique h2
    rw [this]; simp
  exact Complex.ext hre0 him0

/-- Core factorization shared by both `clark_two_node_uncertainty` and `clark_two_node_equality`:
if `f ∈ 𝒢` is real on `ℝ`, `∫ f ≤ 0`, `f(z₁(α)) ≥ 0`, and `f ≥ 0` on `(-∞, u₂]` with `z₂(α) ≤ u₂`,
then `f = c · g_α` for some real `c ≥ 0`. -/
private theorem clark_two_node_factor {α : ℝ} (hα : Real.sin α ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0)
    (hf1 : 0 ≤ (f (clarkNode α 1 : ℂ)).re) {u₂ : ℝ} (hu₂ : clarkNode α 2 ≤ u₂)
    (hfpos : ∀ x : ℝ, x ≤ u₂ → 0 ≤ (f (x : ℂ)).re) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ u : ℂ, f u = (c : ℂ) * clarkExtremal α u := by
  -- 1. Clark quadrature forces `f` to vanish at every Clark node `z_n(α)`
  have hsum := airyClark_hasSum_unc α hα hf hfi hC hb
  have hre := Complex.hasSum_re hsum
  have hw : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      (f z.1 / (deriv airyAiC z.1 ^ 2 - z.1 * airyAiC z.1 ^ 2)).re =
        (f z.1).re / (airyAi' z.1.re ^ 2 - z.1.re * airyAi z.1.re ^ 2) := by
    intro z
    obtain ⟨n, -, hzn⟩ := (psiClark_zero_iff hα z.1).1 z.2
    have him : z.1.im = 0 := by rw [hzn]; simp
    have ez : z.1 = (z.1.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have eK : deriv airyAiC z.1 ^ 2 - z.1 * airyAiC z.1 ^ 2 =
        ((airyAi' z.1.re ^ 2 - z.1.re * airyAi z.1.re ^ 2 : ℝ) : ℂ) := by
      conv_lhs => rw [ez]
      rw [deriv_airyAiC_ofReal, airyAiC_ofReal]
      push_cast; ring
    have ef : f z.1 = (((f z.1).re : ℝ) : ℂ) := by
      conv_lhs => rw [ez]
      exact airy_real_cast hreal z.1.re |>.trans (by rw [← ez])
    conv_lhs => rw [eK, ef, ← Complex.ofReal_div]
    rw [Complex.ofReal_re]
  have hnn_term : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      0 ≤ (f z.1 / (deriv airyAiC z.1 ^ 2 - z.1 * airyAiC z.1 ^ 2)).re := by
    intro z
    rw [hw z]
    have hKpos : 0 < airyAi' z.1.re ^ 2 - z.1.re * airyAi z.1.re ^ 2 := airyKer_pos' _
    obtain ⟨n, hn, hzn⟩ := (psiClark_zero_iff hα z.1).1 z.2
    have hfre : 0 ≤ (f z.1).re := by
      rcases hn.eq_or_lt with rfl | hgt
      · rw [hzn]; exact hf1
      · have hle : z.1.re ≤ u₂ := by
          have hzre : z.1.re = clarkNode α n := by rw [hzn]; simp
          rw [hzre]
          rcases eq_or_ne n 2 with rfl | hn2
          · exact hu₂
          · exact (clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) (by omega) α).le.trans hu₂
        rw [show z.1 = (z.1.re : ℂ) by rw [hzn]; simp]
        exact hfpos _ hle
    exact div_nonneg hfre hKpos.le
  have hint_re : (∫ x : ℝ, f (x : ℂ)).re = ∫ x : ℝ, (f (x : ℂ)).re := by
    simpa using (integral_re hfi).symm
  have hsum0 : (∫ x : ℝ, (f (x : ℂ)).re) = 0 :=
    le_antisymm hint (hint_re ▸ hre.nonneg hnn_term)
  rw [hint_re, hsum0] at hre
  have hall_zero := (hasSum_zero_iff_of_nonneg hnn_term).1 hre
  have hfnodes : ∀ n : ℕ, 1 ≤ n → f (clarkNode α n : ℂ) = 0 := by
    intro n hn
    let z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} :=
      ⟨(clarkNode α n : ℂ), clarkNode_zero hα hn⟩
    have hz0 := congrFun hall_zero z
    simp only [Pi.zero_apply] at hz0
    rw [hw z] at hz0
    have hKpos : 0 < airyAi' z.1.re ^ 2 - z.1.re * airyAi z.1.re ^ 2 := airyKer_pos' _
    have hre0 : (f (clarkNode α n : ℂ)).re = 0 := by
      rcases div_eq_zero_iff.mp hz0 with h | h
      · exact h
      · exact absurd h hKpos.ne'
    exact Complex.ext hre0 (hreal _)
  -- 2. Entire division: `f(u)(u - z₁)(u - z₂) = Q(u) ψ_α(u)²`
  set z₁ := clarkNode α 1 with hz₁
  set z₂ := clarkNode α 2 with hz₂
  set φ : ℂ → ℂ := fun u => f u * ((u - (z₁ : ℂ)) * (u - (z₂ : ℂ))) with hφdef
  have hφ : Differentiable ℂ φ := by fun_prop
  have hzφ : ∀ z : ℂ, psiClark α z = 0 → φ z = 0 ∧ deriv φ z = 0 ∧ deriv (psiClark α) z ≠ 0 := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := (psiClark_zero_iff hα z).1 hz
    have hfn := hfnodes n hn
    have hder : deriv φ (clarkNode α n : ℂ) = 0 := by
      have hd1 : HasDerivAt (fun u : ℂ => (u - (z₁ : ℂ)) * (u - (z₂ : ℂ)))
          (1 * ((clarkNode α n : ℂ) - (z₂ : ℂ)) + ((clarkNode α n : ℂ) - (z₁ : ℂ)) * 1)
          (clarkNode α n : ℂ) :=
        ((hasDerivAt_id _).sub_const _).mul ((hasDerivAt_id _).sub_const _)
      have hd : HasDerivAt φ
          (deriv f (clarkNode α n : ℂ) * (((clarkNode α n : ℂ) - (z₁ : ℂ)) * ((clarkNode α n : ℂ) - (z₂ : ℂ))) +
            f (clarkNode α n : ℂ) * (1 * ((clarkNode α n : ℂ) - (z₂ : ℂ)) + ((clarkNode α n : ℂ) - (z₁ : ℂ)) * 1))
          (clarkNode α n : ℂ) := (hf _).hasDerivAt.mul hd1
      rw [hd.deriv, hfn, zero_mul, add_zero]
      rcases Nat.lt_or_ge n 3 with hlt | hge
      · have h12 : n = 1 ∨ n = 2 := by omega
        rcases h12 with rfl | rfl <;> simp [hz₁, hz₂]
      · have hnlt : clarkNode α n < u₂ :=
          (clarkNode_lt_of_lt (by norm_num : 1 ≤ 2) (by omega) α).trans_le hu₂
        rw [clark_deriv_eq_zero_of_min hf hreal hnlt hfpos hfn, zero_mul]
    refine ⟨by simp [hφdef, hfn], hder, clarkNode_deriv_ne_zero hα hn⟩
  obtain ⟨Q, hQd, hQeq⟩ := EntireDiv.entire_exists_div_sq hφ (differentiable_psiClark α) hzφ
  -- 3. Good-circle bound: `‖Q(u)‖ ≤ C''' (1 + r)²`, so `Q` is a polynomial of degree ≤ 2
  obtain ⟨C', hC', hfb⟩ := airyQ_mem_half hf hfi hC hb
  have hQneg : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  obtain ⟨_, _, k₀, hgc⟩ := airyNC_good_circle (Real.cos α) (-Real.sin α) hQneg
  set c₀ : ℝ := (-Real.sin α) ^ 2 / (256 * π) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  set Cpoly : ℝ := 2 * C' * (1 + |z₁|) * (1 + |z₂|) / c₀ with hCpoly
  have hCpoly0 : 0 ≤ Cpoly := by positivity
  have hcirc : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ u : ℂ, ‖u‖ = r → ‖Q u‖ ≤ Cpoly * (1 + r) ^ 2 := by
    intro R
    set k : ℕ := max (max k₀ 1) ⌈R⌉₊ with hk
    have hk0 : k₀ ≤ k := (le_max_left _ _).trans (le_max_left _ _)
    have hk1 : 1 ≤ k := (le_max_right _ _).trans (le_max_left _ _)
    obtain ⟨r, hr1, _, hgood⟩ := hgc k hk0
    have hrR : R ≤ r := (Nat.le_ceil R).trans ((Nat.cast_le.mpr (le_max_right _ _)).trans hr1)
    have hr_one : 1 ≤ r := (by exact_mod_cast hk1 : (1 : ℝ) ≤ k).trans hr1
    refine ⟨r, hrR, fun u hu => ?_⟩
    have hlow := (hgood u hu).1
    rw [← psiClark_eq_airyNC] at hlow
    have hen := airyEnv_pos u
    have hsr : 0 < √r := Real.sqrt_pos.mpr (by linarith)
    have hnorm := congrArg norm (hQeq u)
    dsimp only [φ] at hnorm
    rw [norm_mul, norm_mul, norm_mul, norm_pow] at hnorm
    have hf_u := hfb u
    rw [hu] at hf_u
    have hz1_u : ‖u - (z₁ : ℂ)‖ ≤ (1 + |z₁|) * (1 + r) := by
      calc ‖u - (z₁ : ℂ)‖ ≤ ‖u‖ + ‖(z₁ : ℂ)‖ := norm_sub_le _ _
        _ = r + |z₁| := by rw [hu, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (1 + |z₁|) * (1 + r) := by nlinarith [abs_nonneg z₁]
    have hz2_u : ‖u - (z₂ : ℂ)‖ ≤ (1 + |z₂|) * (1 + r) := by
      calc ‖u - (z₂ : ℂ)‖ ≤ ‖u‖ + ‖(z₂ : ℂ)‖ := norm_sub_le _ _
        _ = r + |z₂| := by rw [hu, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ (1 + |z₂|) * (1 + r) := by nlinarith [abs_nonneg z₂]
    have h1r : (1 + r) ^ (1 / 2 : ℝ) ≤ 2 * √r := by
      rw [← Real.sqrt_eq_rpow]
      have : 1 + r ≤ 2 * r := by linarith
      calc √(1 + r) ≤ √(2 * r) := Real.sqrt_le_sqrt this
        _ = √2 * √r := Real.sqrt_mul (by norm_num) r
        _ ≤ 2 * √r := by
            have : √2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
            gcongr
    have hdenpos : 0 < c₀ * √r * airyEnv u := by positivity
    have hprod : ‖Q u‖ * (c₀ * √r * airyEnv u) ≤
        C' * (2 * √r) * airyEnv u * ((1 + |z₁|) * (1 + r) * ((1 + |z₂|) * (1 + r))) := by
      calc ‖Q u‖ * (c₀ * √r * airyEnv u) ≤ ‖Q u‖ * ‖psiClark α u‖ ^ 2 := by gcongr
        _ = ‖f u‖ * (‖u - (z₁ : ℂ)‖ * ‖u - (z₂ : ℂ)‖) := hnorm.symm
        _ ≤ (C' * (1 + r) ^ (1 / 2 : ℝ) * airyEnv u) *
              ((1 + |z₁|) * (1 + r) * ((1 + |z₂|) * (1 + r))) := by
            gcongr
        _ ≤ (C' * (2 * √r) * airyEnv u) * ((1 + |z₁|) * (1 + r) * ((1 + |z₂|) * (1 + r))) := by
            gcongr
    have hrhs : C' * (2 * √r) * airyEnv u * ((1 + |z₁|) * (1 + r) * ((1 + |z₂|) * (1 + r))) =
        (Cpoly * (1 + r) ^ 2) * (c₀ * √r * airyEnv u) := by
      rw [hCpoly]; field_simp
    rw [hrhs] at hprod
    exact le_of_mul_le_mul_right hprod hdenpos
  obtain ⟨p, -, hpe⟩ := at47_entire_polynomial_of_circle_bound 2 hQd hCpoly0 hcirc
  -- 4. `f = p · g_α` everywhere, so `L¹(ℝ)` forces `deg p = 0`
  have hfpg : ∀ u : ℂ, f u = p.eval u * clarkExtremal α u := by
    have heq_off : ∀ u : ℂ, u ≠ (z₁ : ℂ) → u ≠ (z₂ : ℂ) → f u = p.eval u * clarkExtremal α u := by
      intro u h1 h2
      have hden : (u - (z₁ : ℂ)) * (u - (z₂ : ℂ)) ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)
      have h1' := hQeq u
      dsimp only [φ] at h1'
      rw [hpe u, ← clarkExtremal_mul_denom hα u] at h1'
      exact mul_right_cancel₀ hden (by linear_combination h1')
    have hfin : ({(z₁ : ℂ), (z₂ : ℂ)} : Set ℂ).Finite := Set.toFinite _
    have hdense : Dense ({(z₁ : ℂ), (z₂ : ℂ)} : Set ℂ)ᶜ := hfin.countable.dense_compl ℂ
    have hcont : Continuous (fun u : ℂ => p.eval u * clarkExtremal α u) :=
      p.continuous.mul (differentiable_clarkExtremal α).continuous
    have hext := Continuous.ext_on hdense hf.continuous hcont fun u hu =>
      heq_off u (fun h => hu (by simp [h])) (fun h => hu (by simp [h]))
    exact congrFun hext
  have hpdeg : p.natDegree = 0 := by
    by_contra hne
    have hp1 : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hne
    refine clark_poly_mul_not_integrable hα p hp1 ?_
    exact hfi.congr (Eventually.of_forall fun x => hfpg (x : ℂ))
  obtain ⟨c₀', hc₀'⟩ : ∃ c₀' : ℂ, ∀ u, p.eval u = c₀' :=
    ⟨p.coeff 0, fun u => by rw [Polynomial.eq_C_of_natDegree_eq_zero hpdeg]; simp⟩
  have hfc₀ : ∀ u : ℂ, f u = c₀' * clarkExtremal α u := fun u => by rw [hfpg u, hc₀' u]
  -- 5. Reality and sign at `a₂ < z₂` give `c₀' = (c : ℂ)` with `0 ≤ c`
  have ha2pos := clarkExtremal_pos_at_airyZero_two hα
  have ha2real : clarkExtremal α (airyZero 2 : ℂ) = (((clarkExtremal α (airyZero 2 : ℂ)).re : ℝ) : ℂ) :=
    airy_real_cast (clarkExtremal_ofReal hα) (airyZero 2)
  have hc₀im : c₀'.im = 0 := by
    have e := congrArg Complex.im (hfc₀ (airyZero 2 : ℂ))
    rw [hreal (airyZero 2), ha2real, Complex.im_mul_ofReal] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact h
    · exact absurd h ha2pos.ne'
  set c : ℝ := c₀'.re with hc
  have hc_cast : c₀' = (c : ℂ) := Complex.ext (by simp [hc]) (by simp [hc₀im])
  have hfc : ∀ u : ℂ, f u = (c : ℂ) * clarkExtremal α u := fun u => by rw [hfc₀ u, hc_cast]
  have hcnn : 0 ≤ c := by
    have ha2_le : airyZero 2 ≤ u₂ := (airyZero_lt_airyClarkNode (by norm_num) _).le.trans hu₂
    have hf2 := hfpos (airyZero 2) ha2_le
    rw [hfc (airyZero 2 : ℂ), ha2real, ← Complex.ofReal_mul, Complex.ofReal_re] at hf2
    exact nonneg_of_mul_nonneg_left hf2 ha2pos
  exact ⟨c, hcnn, hfc⟩

/-- **Clark two-node sign uncertainty** (`clark_airy.tex`, Theorem 1.2):
for `sin α ≠ 0` (in particular for `α ∈ (-π/2, π/2] \ {0}`), if `f ∈ 𝒢 \ {0}` (entire, `f ∈ L¹(ℝ)`,
`‖f u‖ ≤ C (1 + ‖u‖)^ν e(u)`, real on `ℝ`), `∫_ℝ f ≤ 0`, `f(z₁(α)) ≥ 0`, and `f ≥ 0` on `(-∞, u₂]`,
then `u₂ ≤ z₂(α)`. -/
theorem clark_two_node_uncertainty {α : ℝ} (hα : Real.sin α ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0)
    (hf1 : 0 ≤ (f (clarkNode α 1 : ℂ)).re) {u₂ : ℝ}
    (hfpos : ∀ x : ℝ, x ≤ u₂ → 0 ≤ (f (x : ℂ)).re) (hne : ∃ z : ℂ, f z ≠ 0) :
    u₂ ≤ clarkNode α 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hcnn, hfc⟩ := clark_two_node_factor hα hf hfi hC hb hreal hint hf1 hlt.le hfpos
  set x : ℝ := (clarkNode α 2 + min u₂ (clarkNode α 1)) / 2 with hx
  have hlt12 : clarkNode α 2 < min u₂ (clarkNode α 1) := lt_min hlt (clarkNode_two_lt_one α)
  have hx2 : clarkNode α 2 < x := by rw [hx]; linarith
  have hx1 : x < clarkNode α 1 := by rw [hx]; linarith [min_le_right u₂ (clarkNode α 1)]
  have hxu : x ≤ u₂ := by rw [hx]; linarith [min_le_left u₂ (clarkNode α 1)]
  have hgneg : (clarkExtremal α (x : ℂ)).re < 0 := clarkExtremal_neg_between hα hx2 hx1
  have hfxnn : 0 ≤ (f (x : ℂ)).re := hfpos x hxu
  have hgreal : clarkExtremal α (x : ℂ) = (((clarkExtremal α (x : ℂ)).re : ℝ) : ℂ) :=
    airy_real_cast (clarkExtremal_ofReal hα) x
  rw [hfc (x : ℂ), hgreal, ← Complex.ofReal_mul, Complex.ofReal_re] at hfxnn
  have hc0 : c = 0 := by
    have hcle : c ≤ 0 := nonpos_of_mul_nonneg_left hfxnn hgneg
    exact le_antisymm hcle hcnn
  obtain ⟨z, hz⟩ := hne
  apply hz
  rw [hfc z, hc0]
  simp

/-- **Clark two-node equality case** (`clark_airy.tex`, Theorem 1.2):
if `u₂ = z₂(α)`, then `f = c · g_α` for a real constant `c > 0`. -/
theorem clark_two_node_equality {α : ℝ} (hα : Real.sin α ≠ 0) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0)
    (hf1 : 0 ≤ (f (clarkNode α 1 : ℂ)).re)
    (hf2 : ∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (f (x : ℂ)).re) (hne : ∃ z : ℂ, f z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (∀ u : ℂ, f u = (c : ℂ) * clarkExtremal α u) ∧
      ∀ u : ℂ, u ≠ (clarkNode α 1 : ℂ) → u ≠ (clarkNode α 2 : ℂ) →
        f u = (c : ℂ) * psiClark α u ^ 2 / ((u - (clarkNode α 1 : ℂ)) * (u - (clarkNode α 2 : ℂ))) := by
  obtain ⟨c, hcnn, hfc⟩ := clark_two_node_factor hα hf hfi hC hb hreal hint hf1 le_rfl hf2
  have hcne : c ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hne
    apply hz
    rw [hfc z, h0]; simp
  refine ⟨c, lt_of_le_of_ne hcnn hcne.symm, hfc, fun u h1 h2 => ?_⟩
  rw [hfc u, clarkExtremal_eq hα h1 h2]
  ring

/-- **Converse of the Clark two-node equality case**: for every `c > 0`, `c · g_α` satisfies every
hypothesis of the Clark two-node theorem with `u₂ = z₂(α)`. -/
theorem clark_two_node_equality_converse {α : ℝ} (hα : Real.sin α ≠ 0) {c : ℝ} (hc : 0 < c) :
    Differentiable ℂ (fun u : ℂ => (c : ℂ) * clarkExtremal α u) ∧
      Integrable (fun x : ℝ => (c : ℂ) * clarkExtremal α (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖(c : ℂ) * clarkExtremal α u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, ((c : ℂ) * clarkExtremal α (x : ℂ)).im = 0) ∧
      (∫ x : ℝ, ((c : ℂ) * clarkExtremal α (x : ℂ)).re) = 0 ∧
      0 ≤ ((c : ℂ) * clarkExtremal α (clarkNode α 1 : ℂ)).re ∧
      (∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ ((c : ℂ) * clarkExtremal α (x : ℂ)).re) ∧
      (∃ z : ℂ, (c : ℂ) * clarkExtremal α z ≠ 0) := by
  obtain ⟨hd, hi, ⟨C, hC, hb⟩, hreal, hz1, _, hband, _, _, hint, ⟨z, hz⟩⟩ :=
    clarkExtremal_attains hα
  have hre : ∀ x : ℝ, ((c : ℂ) * clarkExtremal α (x : ℂ)).re = c * (clarkExtremal α (x : ℂ)).re := by
    intro x; simp [Complex.mul_re]
  refine ⟨(differentiable_const _).mul hd, hi.const_mul _,
    ⟨c * C, -(3 / 2 : ℝ), by positivity, fun u => ?_⟩,
    fun x => by simp [Complex.mul_im, hreal x],
    ?_,
    by rw [hz1]; simp,
    fun x hx => by rw [hre x]; exact mul_nonneg hc.le (hband x hx),
    ⟨z, mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hz⟩⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    calc c * ‖clarkExtremal α u‖ ≤ c * (C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u) := by gcongr; exact hb u
      _ = c * C * (1 + ‖u‖) ^ (-(3 / 2) : ℝ) * airyEnv u := by ring
  · simp_rw [hre]; rw [integral_const_mul, hint, mul_zero]

/-- **Clark two-node equality, equivalence form** (`clark_airy.tex`, Theorem 1.2):
an entire `f` is in `𝒢 \ {0}`, real on `ℝ`, with `∫ f ≤ 0`, `f(z₁(α)) ≥ 0`, and `f ≥ 0` on `(-∞, z₂(α)]`
**iff** `f = c · g_α` for some real `c > 0`. -/
theorem clark_two_node_equality_iff {α : ℝ} (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} :
    (Differentiable ℂ f ∧ Integrable (fun x : ℝ => f (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (f (x : ℂ)).im = 0) ∧ (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0 ∧
      0 ≤ (f (clarkNode α 1 : ℂ)).re ∧ (∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (f (x : ℂ)).re) ∧
      (∃ z : ℂ, f z ≠ 0)) ↔
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ, f u = (c : ℂ) * clarkExtremal α u := by
  constructor
  · rintro ⟨hf, hfi, ⟨C, ν, hC, hb⟩, hreal, hint, hf1, hf2, hne⟩
    obtain ⟨c, hc, hfc, -⟩ := clark_two_node_equality hα hf hfi hC hb hreal hint hf1 hf2 hne
    exact ⟨c, hc, hfc⟩
  · rintro ⟨c, hc, hfe⟩
    have : f = fun u : ℂ => (c : ℂ) * clarkExtremal α u := funext hfe
    subst this
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := clark_two_node_equality_converse hα hc
    exact ⟨h1, h2, h3, h4, h5.le, h6, h7, h8⟩

/-- **Clark two-node theorem in the `u₁ > a₁` form of `clark_airy.tex` Theorem 1.2**:
given `u₁ > a₁`, let `α ∈ (-π/2, π/2] \ {0}` be the unique angle with `z₁(α) = u₁`. Then for every
`f ∈ 𝒢 \ {0}` with `∫ f ≤ 0`, `f(u₁) ≥ 0`, and `f ≥ 0` on `(-∞, u₂]`, we have `u₂ ≤ z₂(α)`, with
equality iff `f = c · g_α` for some `c > 0`. -/
theorem clark_two_node_of_gt_firstZero {u₁ : ℝ} (hu₁ : airyZero 1 < u₁) :
    ∃! α : ℝ, α ∈ clarkAngleDomain ∧ clarkNode α 1 = u₁ ∧
      (∀ (f : ℂ → ℂ) (C ν : ℝ), Differentiable ℂ f → Integrable (fun x : ℝ => f (x : ℂ)) →
        0 ≤ C → (∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) →
        (∀ x : ℝ, (f (x : ℂ)).im = 0) → (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0 →
        0 ≤ (f (u₁ : ℂ)).re → (∀ {u₂ : ℝ}, (∀ x : ℝ, x ≤ u₂ → 0 ≤ (f (x : ℂ)).re) →
          (∃ z : ℂ, f z ≠ 0) → u₂ ≤ clarkNode α 2)) ∧
      (∀ f : ℂ → ℂ,
        (Differentiable ℂ f ∧ Integrable (fun x : ℝ => f (x : ℂ)) ∧
          (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
          (∀ x : ℝ, (f (x : ℂ)).im = 0) ∧ (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0 ∧
          0 ≤ (f (u₁ : ℂ)).re ∧ (∀ x : ℝ, x ≤ clarkNode α 2 → 0 ≤ (f (x : ℂ)).re) ∧
          (∃ z : ℂ, f z ≠ 0)) ↔
        ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ, f u = (c : ℂ) * clarkExtremal α u) := by
  obtain ⟨α, ⟨hα, hnode⟩, huniq⟩ := existsUnique_clarkAngle_of_gt hu₁
  have hsin := sin_ne_zero_of_mem_clarkAngleDomain hα
  refine ⟨α, ⟨hα, hnode, fun f C ν hf hfi hC hb hreal hint hf1 u₂ hfpos hne => ?_, fun f => ?_⟩, ?_⟩
  · rw [← hnode] at hf1
    exact clark_two_node_uncertainty hsin hf hfi hC hb hreal hint hf1 hfpos hne
  · rw [← hnode]
    exact clark_two_node_equality_iff hsin
  · intro β ⟨hβ, hβnode, _⟩
    exact huniq β ⟨hβ, hβnode⟩

/-- info: 'FormalResearch.SignUncertainty.clark_two_node_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clark_two_node_uncertainty

/-- info: 'FormalResearch.SignUncertainty.clark_two_node_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clark_two_node_equality

/-- info: 'FormalResearch.SignUncertainty.clark_two_node_equality_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clark_two_node_equality_converse

/-- info: 'FormalResearch.SignUncertainty.clark_two_node_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clark_two_node_equality_iff

/-- info: 'FormalResearch.SignUncertainty.clark_two_node_of_gt_firstZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.clark_two_node_of_gt_firstZero


end FormalResearch.SignUncertainty
