module

public import FormalResearch.Special.RacahKappaHLgMatch
public import FormalResearch.Special.RacahKappaCompose

/-!
# Airy window with chart data and a capped radius, half-integer Racah chains (shifted lattice)

Twin of `RacahKappaCompose` for the closed forms `hrAkH`, `hrCkH` on the lattice `q_k = (k + 1) δ³`; declarations carry the suffix `H`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special
/-- The Airy window on the shifted lattice `q_k = (k + 1) δ³` (half-integer chains): `RkWinAtG` with `θ = 1`, `q₀ = δ³`. -/
def RkWinAtH (P Q τ x qs : ℝ) (Y : ℤ → ℝ) (Ymax r C Cmu ξ0 gmin gmax c1 c2 δ : ℝ) (J m N : ℤ) (κ μ : ℝ) : Prop :=
  RkWinAtG 1 (δ ^ 3) P Q τ x qs Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ

/-- The Airy window of `Y` at the scale `h`: `RkWinAtH` for some `δ, J, m, N, κ, μ`. -/
def RkWinH (P Q τ x qs : ℝ) (Y : ℤ → ℝ) (Ymax r δ0 C Cmu ξ0 gmin gmax c1 c2 h : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ^ 3 = h ∧ ∃ (J m N : ℤ) (κ μ : ℝ),
    RkWinAtH P Q τ x qs Y Ymax r C Cmu ξ0 gmin gmax c1 c2 δ J m N κ μ

/-- **Airy window with chart data and a capped radius** (see the module docstring). -/
theorem rk_composeH {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs : ℝ) (hqs : 0 < qs) (hτ : τ ^ 2 = 1)
    (hκ : 0 < 1 - τ * x) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hturn : Phi P Q τ x (qs ^ 2) = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (r δ0 C Cmu ξ0 gmax gmin c1 c2 : ℝ), 0 < r ∧ r ≤ ρ ∧ r ≤ qs / 4 ∧ 0 < δ0 ∧ δ0 ≤ 1 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧
      0 < gmax ∧ 0 < gmin ∧ gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ) (Ymax : ℝ), 0 < h → h ≤ δ0 ^ 3 →
        (∀ k : ℤ, 1 ≤ k → jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) →
        (∀ k : ℤ, qs + h ≤ ((k : ℝ) + 1) * h → |Y k| ≤ Ymax) →
        RkWinH P Q τ x qs Y Ymax r δ0 C Cmu ξ0 gmin gmax c1 c2 h := by
  obtain ⟨r0, hr0, hr0q, hdom⟩ := hr_dom hqs hα hβ
  have hint : 0 < (1 - P * qs ^ 2) * (1 - Q * qs ^ 2) := mul_pos hα hβ
  obtain ⟨r, δ0', C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrr0, hδ0', hδ01, hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, H⟩ :=
    kc2_turn (hrU_contDiffAt τ x 3 hint) (hrU_turn hint hturn)
      (hrU_deriv_pos hqs hκ hα hβ hturn) (hrA_contDiffAt 2 hint) (hrA_pos hint) (lt_min hr0 hρ) (hrE P Q a b qs)
      (hrE_nonneg P Q a b qs)
  have hM0 : 0 < hrM a b := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hδip : 0 < min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (r / 4))) :=
    lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hrr1 : r ≤ r0 := hrr0.trans (min_le_left _ _)
  have hrρ : r ≤ ρ := hrr0.trans (min_le_right _ _)
  refine ⟨r, min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (r / 4)))), C, Cmu, ξ0, gmax, gmin, c1, c2, hr, hrρ,
    hrr1.trans hr0q, lt_min hδ0' hδip, (min_le_right _ _).trans (min_le_left _ _), hC, hCmu, hξ0, hgmax, hgmin, hgg, hc1, hc12, ?_⟩
  intro h Y Ymax hh hhδ hrows hbd
  obtain ⟨δ, hδ, hδ3⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h := by
    refine ⟨h ^ ((1 : ℝ) / 3), Real.rpow_pos_of_pos hh _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le]
    norm_num
  have hδle : δ ≤ min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (r / 4)))) := by
    by_contra hcon
    push Not at hcon
    have : (min δ0' (min 1 (min (3 * qs / (4 * hrM a b)) (min (qs / 2) (r / 4))))) ^ 3 < δ ^ 3 := by gcongr
    linarith
  have hδ1' : δ ≤ δ0' := hδle.trans (min_le_left _ _)
  have hδi' := hδle.trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδi'.trans (min_le_left _ _)
  have hδM : δ ≤ 3 * qs / (4 * hrM a b) := hδi'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδq : δ ≤ qs / 2 := hδi'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr4 : δ ≤ r / 4 := hδi'.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h3δ : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  obtain ⟨J, m, N, hJN, hJm, hmN, hwin, hqJ, hqJc, hqm1, hqm2, hqN, hqN1, hg, hXm, hgl, hgap, hX0m, hXN, Hc⟩ :=
    H δ (δ ^ 3) hδ hδ1'
  have hr4 : r ≤ qs / 4 := hrr1.trans hr0q
  obtain ⟨hpa, hpc⟩ := hrH_perturb hP hQ a b τ x qs hqs hτ hr4 hrr1 hdom hδ hδ1 hδM hwin
  have e2 : ∀ k : ℤ, dalQ (δ ^ 3) δ k = ((k : ℝ) + 1) * δ ^ 3 := fun k => by unfold dalQ; ring
  have Hc' := Hc _ _ hpa hpc
  have hJ1 : 1 ≤ J := hrH_J_pos hr4 hδ (h3δ.trans hδq) (by omega) hwin
  have hrows' : ∀ k ∈ Finset.Icc (J + 1) N,
      jac (hrAkH P Q a b (δ ^ 3)) (hrCkH P Q τ x a b (δ ^ 3)) Y k = 0 := by
    intro k hk
    have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
    rw [hδ3]
    exact hrows k hk1
  have hqN' : qs + δ ^ 3 ≤ ((N : ℝ) + 1) * δ ^ 3 := by have := hqN; rw [e2] at this; linarith
  have hqN1' : qs + δ ^ 3 ≤ (((N + 1 : ℤ) : ℝ) + 1) * δ ^ 3 := by
    push_cast; nlinarith [pow_pos hδ 3]
  obtain ⟨κ, μ, hμ, hpt⟩ := Hc'.pointwise Y Ymax hrows' (hbd N (by rw [← hδ3]; exact hqN')) (hbd (N + 1) (by rw [← hδ3]; exact hqN1'))
  have hYm : 0 ≤ Ymax := (abs_nonneg _).trans (hbd N (by rw [← hδ3]; exact hqN'))
  have hwin' : ∀ k ∈ Finset.Icc J (N + 1), |((k : ℝ) + 1) * δ ^ 3 - qs| ≤ r := by
    intro k hk
    have h1 := hwin k hk
    rw [e2] at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  refine ⟨δ, hδ, hδle, hδ3, J, m, N, κ, μ, hJ1, hJN, hJm, hmN, hwin', ?_, ?_, ?_, ?_,
    ?_, ?_, hg, hXm, hgl, hgap, hX0m, hXN, ?_, hpt⟩
  · rw [← e2]; exact hqJ
  · rw [← e2]; exact hqJc
  · rw [← e2]; exact hqm1
  · rw [← e2]; exact hqm2
  · rw [← e2]; exact hqN
  · have := hqN1; rw [show ((N : ℝ) + 1 + 1) * δ ^ 3 = dalQ (δ ^ 3) δ (N + 1) by
      unfold dalQ; push_cast; ring]; exact this
  · refine hμ.trans ?_
    have hxi := Hc'.1
    have : Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3) δ N)) ≤ Real.exp (-ξ0 / δ ^ 3) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      exact neg_le_neg hxi
    have : Cmu * Ymax * Real.exp (-airyXi (turnX (hrU P Q τ x) qs (δ ^ 3) δ N)) ≤
        Cmu * Ymax * Real.exp (-ξ0 / δ ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
    exact div_le_div_of_nonneg_right this hδ.le


/-- info: 'FormalResearch.Special.rk_composeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_composeH

end FormalResearch.Special
