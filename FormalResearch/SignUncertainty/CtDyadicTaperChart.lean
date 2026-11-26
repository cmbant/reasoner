module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaper
public import FormalResearch.SignUncertainty.CtBoasSigmaLip
public import FormalResearch.SignUncertainty.CtLowerDefs

/-!
# `ct:dyadic` (4): the taper `w̃_R(ξ(L))` for the concrete Hankel chart, and the taper inputs of `ct:boas`

`constant_terms_lower.tex`, `ct:dyadic` (4): `w_R(v) = 1 - W₆(-v)`, `R' = -φ_c(-R)`, and the `C¹` taper
`w̃_R(ξ) = w_R(-û(ũ(ξ)))` on `ξ ∈ [ξ(0), ξ(-R')]`, `w̃_R = 1` for `ξ > ξ(-R')`; in the band variable `L = log(π²ξ)`
(`ξ(L) = e^L/π²`, so `Δ = cξ`) it is `ctTaper ε c R L`, with `0` for `L ≤ 0` (the extension below `ξ(0)` used by the field
`trunc_lo` of `BoasInputs`).  Objects: `ctUtildeXi` (`ũ(ξ)`, the inverse of the Lean chart `hankelXi` on `[-A, 0]`), `ctRprime`
(`R'`), `ctTaperLam` (`Λ = L(ξ(-R'))`), `ctTaperV` (`v(L) = -û(ũ(ξ(L)))`, `ct:taper-harnack` (c)), `ctTaper`.

`TaperChartInputs ε c R A` is the named hypothesis structure for what the chart supplies (`ct:taper-harnack` (c), first half;
`ct:Bj-pointwise` notation `Λ ≍ 1`): `v > 0` nondecreasing with `L ∂_L log v ≤ A_v` (in the integral form of `TaperProfile`)
on `(0, Λ]`, `v(Λ) ≥ R` (equality by `R' = -φ_c(-R)`, `ct:cfu`), and `0 < Λ ≤ log(π² log c / 2)` (so that
`Δ > D/2` forces `L > Λ`).  Proved from the Lean chart and the `ψ_ε` window in `CtDyadicTaperBuild` (`taperChartInputs`, `A_v = 2`, unconditional).

Discharged from `TaperChartInputs`: `ctTaper_hwt1` (`w̃ = 1` for `Δ > D/2`, the hypothesis `hwt1` of `boas_far_field`),
`TaperChartInputs.reg` (`TaperReg`), and `ctTaper_block_bounds` (the hypotheses `hlip`, `hSup` of `boas_freeze_field` and
`hMp_bd`, `hS_bd` of `boas_pointwise_field` for `wt = ctTaper`, `sf = 𝔰_far(Δ(L))`, `Msig j = sigLip` at the right end of `Q_j`,
`Mp = tapMp`, `S = tapS`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `ũ(ξ)`: the inverse of the Lean Langer chart `hankelXi` on `[-A, 0]`, `A = langerRadius c`. -/
noncomputable def ctUtildeXi (c ξ : ℝ) : ℝ :=
  Function.invFunOn (hankelXi c) (Icc (-(langerRadius c)) 0) ξ

/-- `R' = -φ_c(-R)` (`ct:dyadic` (4)). -/
noncomputable def ctRprime (ε c R : ℝ) : ℝ := -ctPhi ε c (-R)

/-- `Λ = L(ξ(-R')) = log(π² ξ(-R'))` (`ct:Bj-pointwise` notation), `ξ(ũ) = hankelXi c ũ`. -/
noncomputable def ctTaperLam (ε c R : ℝ) : ℝ := Real.log (π ^ 2 * hankelXi c (-(ctRprime ε c R)))

/-- `v(L) = -û(ũ(ξ(L)))`, `ξ(L) = e^L/π²` (`ct:taper-harnack` (c)). -/
noncomputable def ctTaperV (ε c L : ℝ) : ℝ := -ctUhat ε c (ctUtildeXi c (Real.exp L / π ^ 2))

/-- The taper in the band variable: `w̃_R(ξ(L)) = w_R(v(L))` for `0 < L ≤ Λ`, `1` for `L > Λ`, `0` for `L ≤ 0`. -/
noncomputable def ctTaper (ε c R L : ℝ) : ℝ :=
  if L ≤ 0 then 0 else taperW R (if L ≤ ctTaperLam ε c R then ctTaperV ε c L else R)

/-- **The chart inputs of the taper** (see the module docstring). -/
structure TaperChartInputs (ε c R A : ℝ) : Prop where
  R_pos : 0 < R
  one_le_A : 1 ≤ A
  Lam_pos : 0 < ctTaperLam ε c R
  Lam_le : ctTaperLam ε c R ≤ Real.log (π ^ 2 * Real.log c / 2)
  v_pos : ∀ L, 0 < L → L ≤ ctTaperLam ε c R → 0 < ctTaperV ε c L
  v_mono : ∀ L L', 0 < L → L ≤ L' → L' ≤ ctTaperLam ε c R → ctTaperV ε c L ≤ ctTaperV ε c L'
  v_ratio : ∀ L L', 0 < L → L ≤ L' → L' ≤ ctTaperLam ε c R →
    ctTaperV ε c L' ≤ (L' / L) ^ A * ctTaperV ε c L
  v_Lam : R ≤ ctTaperV ε c (ctTaperLam ε c R)

section

variable {ε c R A : ℝ}

/-- The glued and clamped profile `min(R, v(L))` (`v` for `L ≤ Λ`, `R` beyond). -/
noncomputable def ctTaperVbar (ε c R L : ℝ) : ℝ :=
  min R (if L ≤ ctTaperLam ε c R then ctTaperV ε c L else R)

lemma TaperChartInputs.profile (I : TaperChartInputs ε c R A) : TaperProfile R A (ctTaperVbar ε c R) where
  R_pos := I.R_pos
  one_le_A := I.one_le_A
  v_pos := by
    intro L hL
    unfold ctTaperVbar
    refine lt_min I.R_pos ?_
    split_ifs with h
    · exact I.v_pos L hL h
    · exact I.R_pos
  v_mono := by
    intro L L' hL hLL
    unfold ctTaperVbar
    by_cases h' : L' ≤ ctTaperLam ε c R
    · have h : L ≤ ctTaperLam ε c R := hLL.trans h'
      rw [if_pos h, if_pos h']
      exact min_le_min le_rfl (I.v_mono L L' hL hLL h')
    · rw [if_neg h', min_self]; exact min_le_left _ _
  v_ratio := by
    intro L L' hL hLL
    have hL' : 0 < L' := lt_of_lt_of_le hL hLL
    have hρ : 1 ≤ (L' / L) ^ A :=
      Real.one_le_rpow ((one_le_div hL).2 hLL) (by linarith [I.one_le_A])
    have hR := I.R_pos
    unfold ctTaperVbar
    by_cases h' : L' ≤ ctTaperLam ε c R
    · have h : L ≤ ctTaperLam ε c R := hLL.trans h'
      rw [if_pos h, if_pos h']
      have hv := I.v_pos L hL h
      have hr := I.v_ratio L L' hL hLL h'
      by_cases hVR : ctTaperV ε c L ≤ R
      · rw [min_eq_right hVR]
        exact (min_le_right _ _).trans hr
      · rw [not_le] at hVR
        have hm := I.v_mono L L' hL hLL h'
        rw [min_eq_left hVR.le, min_eq_left (hVR.le.trans hm)]
        nlinarith
    · rw [if_neg h', min_self]
      by_cases h : L ≤ ctTaperLam ε c R
      · rw [if_pos h]
        by_cases hVR : ctTaperV ε c L ≤ R
        · rw [min_eq_right hVR]
          have h1 := I.v_ratio L (ctTaperLam ε c R) hL h le_rfl
          have h2 : (ctTaperLam ε c R / L) ^ A ≤ (L' / L) ^ A :=
            Real.rpow_le_rpow (div_pos I.Lam_pos hL).le
              (div_le_div_of_nonneg_right (not_le.1 h').le hL.le) (by linarith [I.one_le_A])
          have hv := I.v_pos L hL h
          calc R ≤ ctTaperV ε c (ctTaperLam ε c R) := I.v_Lam
            _ ≤ (ctTaperLam ε c R / L) ^ A * ctTaperV ε c L := h1
            _ ≤ (L' / L) ^ A * ctTaperV ε c L := mul_le_mul_of_nonneg_right h2 hv.le
        · rw [not_le] at hVR
          rw [min_eq_left hVR.le]; nlinarith
      · rw [if_neg h, min_self]; nlinarith

lemma taper_min_eq (R x : ℝ) : taperW R (min R x) = taperW R x := by
  unfold taperW taperX
  rw [min_comm R x, min_assoc, min_self]

/-- The taper agrees with `w_R ∘ v̄` on `L > 0`. -/
lemma ctTaper_eq_of_pos (ε c R : ℝ) {L : ℝ} (hL : 0 < L) :
    ctTaper ε c R L = taperW R (ctTaperVbar ε c R L) := by
  unfold ctTaper ctTaperVbar
  rw [if_neg (not_le.2 hL), taper_min_eq]

/-- **`TaperReg` for the concrete taper** (`ct:taper-harnack`): from the chart inputs. -/
theorem TaperChartInputs.reg (I : TaperChartInputs ε c R A) : TaperReg (ctTaper ε c R) A (taperKw A) := by
  have hr := I.profile.reg
  have hmem : ∀ L, 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1 := by
    intro L
    unfold ctTaper
    split_ifs <;>
      first
      | exact ⟨le_rfl, zero_le_one⟩
      | exact ⟨taperW_nonneg I.R_pos _, taperW_le_one I.R_pos _⟩
  refine ⟨hr.A_nonneg, hr.Kw_nonneg, hmem, ?_, ?_, ?_⟩
  · intro L L' hL hLL
    rw [ctTaper_eq_of_pos ε c R hL, ctTaper_eq_of_pos ε c R (hL.trans_le hLL)]
    exact hr.mono L L' hL hLL
  · intro L L' hL hLL
    rw [ctTaper_eq_of_pos ε c R hL, ctTaper_eq_of_pos ε c R (hL.trans_le hLL)]
    exact hr.loglip L L' hL hLL
  · intro L L' hL hLL h3
    rw [ctTaper_eq_of_pos ε c R hL, ctTaper_eq_of_pos ε c R (hL.trans_le hLL)]
    exact hr.harnack L L' hL hLL h3

/-- **`hwt1`** of `boas_far_field`: `w̃ = 1` for `Δ = c e^L/π² > D/2 = c log c/2` (`Λ ≤ log(π² log c/2)`). -/
theorem ctTaper_hwt1 (hc : 1 < c) (I : TaperChartInputs ε c R A) :
    ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) → ctTaper ε c R L = 1 := by
  intro L hL
  have hc0 : 0 < c := by linarith
  have hlog : 0 < Real.log c := Real.log_pos hc
  have hπ : 0 < π ^ 2 := by positivity
  have h1 : π ^ 2 * Real.log c / 2 < Real.exp L := by
    unfold farD at hL
    have : c * (Real.log c / 2) < c * (Real.exp L / π ^ 2) := by linarith
    have := lt_of_mul_lt_mul_left this hc0.le
    rw [lt_div_iff₀ hπ] at this; linarith
  have h2 : Real.log (π ^ 2 * Real.log c / 2) < L := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]; exact h1
  have hLam : ctTaperLam ε c R < L := lt_of_le_of_lt I.Lam_le h2
  unfold ctTaper
  rw [if_neg (not_le.2 (I.Lam_pos.trans hLam)), if_neg (not_le.2 hLam)]
  exact taperW_of_ge I.R_pos le_rfl

end

/-- The Lipschitz constant `M_j^σ` of `σ = 1 - 𝔰_far` on `Q_j`: `sigLip` at the right end of `Q_j`. -/
noncomputable def tapMsig (c a : ℝ) (j : ℕ) : ℝ := sigLip c (tentNode a (j + 1) + 3 * tentDelta a j)

/-- **The taper inputs of `ct:boas` Step 5** for `wt = ctTaper`, `sf = 𝔰_far(Δ(L))`, `Mp = tapMp`, `S = tapS`,
`Msig = tapMsig`, `Kmp = (13/12)K₀` with `K₀ = taperK0 A`: the hypotheses `hlip`, `hSup` of `boas_freeze_field` and `hMp_bd`,
`hS_bd` of `boas_pointwise_field` (`ct:taper-harnack`, `ct:sigma-prime`), from `TaperChartInputs`. -/
theorem ctTaper_block_bounds {ε c R A a : ℝ} (hc : 1 < c) (ha : 0 < a) (I : TaperChartInputs ε c R A) :
    (∀ j, ∀ L ∈ tentQ a j, ∀ L0 ∈ tentQ a j,
      |ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * tent (tentNode a) j L -
          ctTaper ε c R L0 * (1 - sFar c (c * (Real.exp L0 / π ^ 2))) * tent (tentNode a) j L0| ≤
        tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 A) a j * |L - L0|) ∧
    (∀ j, ∀ L ∈ tentQ a j,
      ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * tent (tentNode a) j L ≤
        tapS (ctTaper ε c R) (taperKw A) a j) ∧
    (∀ j, ∀ L ∈ tentQ a j, tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 A) a j ≤
      tapMsig c a j + 13 / 12 * taperK0 A * ctTaper ε c R L / min L 1) ∧
    (∀ j, ∀ L ∈ tentQ a j, tapS (ctTaper ε c R) (taperKw A) a j ≤ taperKw A * ctTaper ε c R L) := by
  have hreg := I.reg
  have hsf : ∀ L, 0 ≤ sFar c (c * (Real.exp L / π ^ 2)) ∧ sFar c (c * (Real.exp L / π ^ 2)) ≤ 1 :=
    fun L => ⟨sFar_nonneg hc _, sFar_le_one hc _⟩
  have hσ : ∀ j, ∀ L ∈ tentQ a j, ∀ L0 ∈ tentQ a j,
      |sFar c (c * (Real.exp L / π ^ 2)) - sFar c (c * (Real.exp L0 / π ^ 2))| ≤ tapMsig c a j * |L - L0| :=
    fun j L hL L0 hL0 => sFar_lipschitz_log hc (Rt := tentNode a (j + 1) + 3 * tentDelta a j) hL.2 hL0.2
  exact ⟨taper_hlip hreg ha hsf hσ, taper_hSup hreg ha hsf, taper_hMp_bd hreg ha _, taper_hS_bd hreg ha⟩

/-- info: 'FormalResearch.SignUncertainty.ctTaper_block_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctTaper_block_bounds

/-- info: 'FormalResearch.SignUncertainty.ctTaper_hwt1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctTaper_hwt1

end FormalResearch.SignUncertainty
