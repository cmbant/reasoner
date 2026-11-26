/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSymCal
public import FormalResearch.SignUncertainty.FctBump5
public import FormalResearch.SignUncertainty.UctStripSplit

/-!
# `fct:bump-sym-check` (Lemma FCT.7b): the physical bump is a finite sum of symbol-class profiles (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.7b (`fct:bump-sym-check`) with the bump
`(fct:B-physical)`.  The bump is
`B = n_c χ(L/3δ) γ(L̃) [(1 + η) O − (1 − η) F] + B_tr`, `F = (L̃/(L − L₁)) I_fl(L̃)`, `O = I_osc^{warp}`,
`η = K₁(c^{-2}L^{-2} + c^{-1})`, `γ(L̃) = 1 − (5π²/96) c^{-2} L̃^{-3}`, `L̃ = L − s` (`s = θ₁^ε/c`).

**What is proved** (`FctSymCal` supplies the calculus; all constants explicit and independent of `c`):

* `physGamma_sym`, `physF_sym`: the *explicit* factors `γ(L̃)` and `F` are profiles of weight `1` and `α_fl L^{-3/2}`
  (Lemma 7b (a): `γ(L̃) − 1`, `L̃/(L − L₁) − 1` and the cutoff `χ(L/3δ)` are symbols of order `0`).
* `physBump_pieces`: for `O = F R`, the four pieces of Lemma 7b (c) (`B_diff`, the two margin pieces, `B_tr`) obey `(fct:B-sym)` with
  `(M, α, β)` obtained by the class arithmetic `(α₁,β₁)·(α₂,β₂) = (α₁+α₂, β₁+β₂)`:
  `F ∈ (M_Φ, α_Φ, β_Φ)`, `R − 1 ∈ (M_R, -1, 0)` give `B_diff ∈ (M_Φ M_R, α_Φ − 1, β_Φ)` (for `H_*`, `H_CE`: `(1/2, 3/2)`),
  margin `(…c^{-2}, α_Φ + 2, β_Φ + 2)` (`(7/2, 7/2)`) and `(…c^{-1}, α_Φ, β_Φ)` (`(3/2, 3/2)`), `B_tr ∈ (·, -1/2, 3/2)`.
* `physBump_profile`: the bump itself is a `BumpProfile (3/2) δ M (7/2) (3/2) K`, with `K` independent of `c`.

**Hypotheses (named after the paper's inputs, not proved here).**  `hR` (`R = O/F`, `R − 1 ∈ (M_R, -1, 0)` on `[3δ/2, ∞)`):
the paper's "`r₀ e^v (1 + Δ_curv) · |1 − L₁ φ_kill/L̃| − 1` has `r`-th `L`-derivative `O_{K₄}(L^{1-r})` on `[3δ/2, 1]` and is a symbol of
order `0` beyond", i.e. Lemma 7b (b) (`fct:comp-D` (1), `(fct:th-tail)`, `fct:phikill` (1), super-exponential decay of `I_osc`);
`hT` (`τ₀⁴ I_fl ∈ (M_T, -1/2, 3/2)` on `[3δ/2, 6δ]`, from `m(t) = t² n₂(t²)`).

Class: proved under the explicit hypotheses `hR`, `hT`.  Axiom guards at the end.
-/

@[expose] public section

open Set Finset
open scoped ContDiff Real

namespace FormalResearch.SignUncertainty.FctSym

open SymW

/-- `γ(L̃) = 1 − (5π²/96) c^{-2} L̃^{-3}`, `L̃ = L − s` (`fct:warp-asymp` (3)). -/
noncomputable def physGamma (c s x : ℝ) : ℝ := 1 - (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (x - s) ^ (-3 : ℝ)

/-- `F(L) = (L̃/(L − L₁)) I_fl(L̃)`, `L̃ = L − s`. -/
noncomputable def physF (s L1 x : ℝ) : ℝ := (x - s) / (x - L1) * uctIfl (x - s)

/-- `γ(L̃)` is a profile of weight `1` and order `0` on `[x₀, ∞)` once `(5π²/96) c^{-2} x₀^{-3} ≤ 1` and `|s| ≤ x₀/2`. -/
lemma physGamma_sym {x₀ c s : ℝ} (hx₀ : 0 < x₀) (hs : |s| ≤ x₀ / 2)
    (hsmall : (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * x₀ ^ (-3 : ℝ) ≤ 1) :
    SymW (Ici x₀) (fun _ => 1) (fun r => Kone r + Kpow (-3) r) (physGamma c s) := by
  have h1 : SymW (Ici x₀) (fun _ => 1) Kone (fun _ => (1 : ℝ)) :=
    (SymW.const (fun x hx => lt_of_lt_of_le hx₀ hx) 1).of_le (fun x _ => by simp) (fun _ => le_rfl)
  have h2 : SymW (Ici x₀) (fun _ => 1) (Kpow (-3))
      (fun x => (-((5 * π ^ 2 / 96) * c⁻¹ ^ 2)) * (x - s) ^ (-3 : ℝ)) := by
    refine (SymW.rpow_sub hx₀ (-((5 * π ^ 2 / 96) * c⁻¹ ^ 2)) (-3) s hs).of_le (fun x hx => ?_) (fun _ => le_rfl)
    have hxp : 0 < x₀ := hx₀
    have hxx : x₀ ≤ x := hx
    have h3 : x ^ (-3 : ℝ) ≤ x₀ ^ (-3 : ℝ) := Real.rpow_le_rpow_of_nonpos hx₀ hxx (by norm_num)
    have h4 : 0 ≤ (5 * π ^ 2 / 96) * c⁻¹ ^ 2 := by positivity
    rw [abs_neg, abs_of_nonneg h4]
    calc (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * x ^ (-3 : ℝ) ≤ (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * x₀ ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_left h3 h4
      _ ≤ 1 := hsmall
  refine (h1.add h2).congr (U := univ) isOpen_univ (subset_univ _) fun x _ => ?_
  simp only [physGamma]; ring

/-- `F = (L̃/(L − L₁)) I_fl(L̃)` is a profile of weight `α_fl L^{-3/2}` on `[x₀, ∞)` when `|s|, |L₁| ≤ x₀/2`, `|L₁ − s| ≤ x₀`
(`L̃/(L − L₁) = 1 + (L₁ − s)/(L − L₁)`). -/
lemma physF_sym {x₀ s L1 : ℝ} (hx₀ : 0 < x₀) (hs : |s| ≤ x₀ / 2) (hL1 : |L1| ≤ x₀ / 2) (hL : |L1 - s| ≤ x₀) :
    SymW (Ici x₀) (pw |uctAlphaFl| (3 / 2) (3 / 2)) (Kmul (fun r => Kone r + Kpow (-1) r) (Kpow (-(3 / 2))))
      (physF s L1) := by
  have h1 : SymW (Ici x₀) (fun _ => 1) Kone (fun _ => (1 : ℝ)) :=
    (SymW.const (fun x hx => lt_of_lt_of_le hx₀ hx) 1).of_le (fun x _ => by simp) (fun _ => le_rfl)
  have h2 : SymW (Ici x₀) (fun _ => 1) (Kpow (-1)) (fun x => (L1 - s) * (x - L1) ^ (-1 : ℝ)) := by
    refine (SymW.rpow_sub hx₀ (L1 - s) (-1) L1 hL1).of_le (fun x hx => ?_) (fun _ => le_rfl)
    have hxx : x₀ ≤ x := hx
    have h3 : x ^ (-1 : ℝ) ≤ x₀ ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos hx₀ hxx (by norm_num)
    simp only [Real.rpow_neg_one] at h3 ⊢
    calc |L1 - s| * x⁻¹ ≤ x₀ * x₀⁻¹ := mul_le_mul hL h3 (inv_nonneg.mpr (by linarith)) hx₀.le
      _ = 1 := mul_inv_cancel₀ hx₀.ne'
  have hP := h1.add h2
  have hI := SymW.rpow_sub hx₀ uctAlphaFl (-(3 / 2)) s hs
  have hm := hP.mul hI
  refine (hm.of_le (fun x hx => ?_) (fun _ => le_rfl)).congr (U := Ioi (x₀ / 2)) isOpen_Ioi
    (fun x hx => by have : x₀ ≤ x := hx; exact Set.mem_Ioi.mpr (by linarith)) fun x hx => ?_
  · rw [pw_self, show -(3 / 2 : ℝ) = -(3 / 2) from rfl]; linarith
  · have hx' : x₀ / 2 < x := hx
    have h5 : 0 < x - L1 := by linarith [(abs_le.mp hL1).2]
    simp only [physF, uctIfl]
    rw [Real.rpow_neg_one]
    field_simp
    ring

lemma pw_scale (a M α β x : ℝ) : a * pw M α β x = pw (a * M) α β x := by unfold pw; ring

/-- `γ`-constants. -/
noncomputable def Kgam (r : ℕ) : ℝ := Kone r + Kpow (-3) r

/-- The constants of the four pieces of Lemma FCT.7b (c): they depend only on the constants of the cutoff (`Kχ`) and of the
inputs `F` (`KΦ`), `R − 1` (`KR`), `τ₀⁴ I_fl` (`KT`). -/
noncomputable def KpDiff (Kχ KΦ KR : ℕ → ℝ) : ℕ → ℝ := Kmul (Kmul Kχ Kgam) (Kmul KΦ KR)

noncomputable def KpMar1 (Kχ KΦ KR : ℕ → ℝ) : ℕ → ℝ :=
  Kmul (Kmul Kχ Kgam) (Kmul (Kpow (-2)) (Kmul KΦ (fun r => KR r + Kone r)))

noncomputable def KpMar2 (Kχ KΦ KR : ℕ → ℝ) : ℕ → ℝ :=
  Kmul (Kmul Kχ Kgam) (Kmul Kone (Kmul KΦ (fun r => KR r + Kone r)))

noncomputable def KpTr (Kχ KT : ℕ → ℝ) : ℕ → ℝ := Kmul Kχ (Kmul (fun r => Kone r + Kχ r) KT)

/-- **Lemma FCT.7b (c)** for the common physical bump `(fct:B-physical)`, in the uniform form: with `F ∈ (M_Φ, α_Φ, β_Φ)` and
`O = F R`, `R − 1 ∈ (M_R, -1, 0)` (`(fct:B-sym)` on `[3δ/2, ∞)`, the inputs of 7b (a)-(b)), and `τ₀⁴ I_fl ∈ (M_T, -1/2, 3/2)` on
`[3δ/2, 6δ]`:

* `B_diff = χ γ (O − F) ∈ (M_Φ M_R, α_Φ − 1, β_Φ)`;
* the margin `χ γ η (O + F)` splits into `χ γ K₁c^{-2}L^{-2}(O + F) ∈ (|K₁c^{-2}| M_Φ (M_R + 2), α_Φ + 2, β_Φ + 2)` and
  `χ γ K₁c^{-1}(O + F) ∈ (|K₁c^{-1}| M_Φ (M_R + 2), α_Φ, β_Φ)`;
* `2K₄ χ(L/3δ)(1 − χ(L/6δ)) τ₀⁴ I_fl ∈ (2|K₄| M_T, -1/2, 3/2)`.

The constants `K` are the explicit functions `KpDiff`, `KpMar1`, `KpMar2`, `KpTr` of `Kχ, KΦ, KR, KT`, independent of `c, δ, s, K₁, K₄`. -/
theorem physBump_pieces {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Kχ : ℕ → ℝ} (hKχ : ∀ (r : ℕ) (s : ℝ), |iteratedDeriv r χ s| ≤ Kχ r)
    {KΦ KR KT : ℕ → ℝ} {c δ s K1 K4 MΦ αΦ βΦ MR MT : ℝ} {F R T4 : ℝ → ℝ}
    (hδ : 0 < δ) (hs : |s| ≤ 3 / 2 * δ / 2) (hsmall : (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δ) ^ (-3 : ℝ) ≤ 1)
    (hMR : 0 ≤ MR) (hMT : 0 ≤ MT)
    (hF : SymW (Ici (3 / 2 * δ)) (pw MΦ αΦ βΦ) KΦ F)
    (hR : SymW (Ici (3 / 2 * δ)) (pw MR (-1) 0) KR (fun x => R x - 1))
    (hT : SymW (Icc (3 / 2 * δ) (6 * δ)) (pw MT (-(1 / 2)) (3 / 2)) KT T4) :
    SymW (Ici (3 / 2 * δ)) (pw (MΦ * MR) (αΦ - 1) βΦ) (KpDiff Kχ KΦ KR)
        (fun x => χ (x / (3 * δ)) * physGamma c s x * (F x * R x - F x)) ∧
      SymW (Ici (3 / 2 * δ)) (pw (|K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2))) (αΦ + 2) (βΦ + 2)) (KpMar1 Kχ KΦ KR)
        (fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ ^ 2 * x ^ (-2 : ℝ) * (F x * R x + F x))) ∧
      SymW (Ici (3 / 2 * δ)) (pw (|K1 * c⁻¹| * (MΦ * (MR + 2))) αΦ βΦ) (KpMar2 Kχ KΦ KR)
        (fun x => χ (x / (3 * δ)) * physGamma c s x * (K1 * c⁻¹ * (F x * R x + F x))) ∧
      SymW (Ici (3 / 2 * δ)) (pw (|2 * K4| * MT) (-(1 / 2)) (3 / 2)) (KpTr Kχ KT)
        (fun x => 2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * T4 x))) := by
  have hx0 : 0 < 3 / 2 * δ := by positivity
  have hxpos : ∀ x ∈ Ici (3 / 2 * δ), 0 < x := fun x hx => lt_of_lt_of_le hx0 hx
  have hχ3 : SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kχ (fun x => χ (x / (3 * δ))) := hχ.symW hKχ (by positivity) hxpos
  have hχ6 : SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kχ (fun x => χ (x / (6 * δ))) := hχ.symW hKχ (by positivity) hxpos
  have hγ := physGamma_sym hx0 hs hsmall
  have hG := hχ3.mul hγ
  -- the shifted sum `R + 1 = (R - 1) + 2`
  have hRc : SymW (Ici (3 / 2 * δ)) (fun _ => MR + 2) KR (fun x => R x - 1) :=
    hR.of_le (fun x hx => (pw_const_le hMR (by norm_num) (by norm_num) (hxpos x hx)).trans (by linarith)) (fun _ => le_rfl)
  have h2c : SymW (Ici (3 / 2 * δ)) (fun _ => MR + 2) Kone (fun _ => (2 : ℝ)) :=
    (SymW.const hxpos 2).of_le (fun x _ => by simp; linarith) (fun _ => le_rfl)
  have hR1 := hRc.add h2c
  have hFR1 := hF.mul hR1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hG.mul (hF.mul hR)
    refine (h.of_le (fun x hx => ?_) (fun _ => le_rfl)).congr (U := univ) isOpen_univ (subset_univ _) fun x _ => ?_
    · have hxp := hxpos x hx
      have e := pw_mul MΦ MR αΦ (-1) βΦ 0 x hxp
      refine le_of_eq ?_
      rw [one_mul, one_mul, e, show αΦ + -1 = αΦ - 1 by ring, add_zero]
    · ring
  · have h := hG.mul ((rpow0 hx0 (K1 * c⁻¹ ^ 2) (-2)).mul hFR1)
    refine (h.of_le (fun x hx => ?_) (fun _ => le_rfl)).congr (U := univ) isOpen_univ (subset_univ _) fun x _ => ?_
    · have hxp := hxpos x hx
      have e1 : x ^ (-2 : ℝ) = pw 1 2 2 x := by rw [pw_self]; simp
      have e2 : (MR + 2) = pw (MR + 2) 0 0 x := (pw_zero _ _).symm
      calc 1 * 1 * (|K1 * c⁻¹ ^ 2| * x ^ (-2 : ℝ) * (pw MΦ αΦ βΦ x * (MR + 2)))
          = pw (|K1 * c⁻¹ ^ 2|) 2 2 x * (pw MΦ αΦ βΦ x * pw (MR + 2) 0 0 x) := by
            rw [pw_zero, pw_self]; ring
        _ ≤ _ := le_of_eq (by
            rw [pw_mul _ _ _ _ _ _ x hxp, pw_mul _ _ _ _ _ _ x hxp, show (2 : ℝ) + (αΦ + 0) = αΦ + 2 by ring,
              show (2 : ℝ) + (βΦ + 0) = βΦ + 2 by ring])
    · ring
  · have h := hG.mul ((SymW.const hxpos (K1 * c⁻¹)).mul hFR1)
    refine (h.of_le (fun x hx => ?_) (fun _ => le_rfl)).congr (U := univ) isOpen_univ (subset_univ _) fun x _ => ?_
    · have hxp := hxpos x hx
      calc 1 * 1 * (|K1 * c⁻¹| * (pw MΦ αΦ βΦ x * (MR + 2)))
          = pw (|K1 * c⁻¹| * (MΦ * (MR + 2))) αΦ βΦ x := by unfold pw; ring
        _ ≤ _ := le_rfl
    · ring
  · have hone : SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kone (fun _ => (1 : ℝ)) :=
      (SymW.const hxpos 1).of_le (fun x _ => by simp) (fun _ => le_rfl)
    have hneg : SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kχ (fun x => (-1 : ℝ) * χ (x / (6 * δ))) :=
      (hχ6.smul (-1)).of_le (fun x _ => by simp) (fun _ => le_rfl)
    have hcut := (hone.add hneg).congr (U := univ) isOpen_univ (subset_univ _)
      (g := fun x => 1 - χ (x / (6 * δ))) fun x _ => by ring
    have hcutT := (hcut.mono_set (S' := Icc (3 / 2 * δ) (6 * δ)) (fun x (hx : x ∈ Icc (3 / 2 * δ) (6 * δ)) => hx.1)).mul hT
    have hext : SymW (Ici (3 / 2 * δ)) (fun x => 1 * pw MT (-(1 / 2)) (3 / 2) x) (Kmul (fun r => Kone r + Kχ r) KT)
        (fun x => (1 - χ (x / (6 * δ))) * T4 x) := by
      refine SymW.extend_zero hx0 hcutT (x₂ := 6 * δ) (fun x hx => ?_) (fun x hx => ?_)
      · have : 1 ≤ x / (6 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
        rw [hχ.one _ this]; ring
      · have hxp : 0 < x := by linarith
        exact mul_nonneg zero_le_one (pw_nonneg hMT hxp)
    have h := (hχ3.mul hext).smul (2 * K4)
    refine (h.of_le (fun x hx => ?_) (fun _ => le_rfl)).congr (U := univ) isOpen_univ (subset_univ _) fun x _ => ?_
    · calc |2 * K4| * (1 * (1 * pw MT (-(1 / 2)) (3 / 2) x)) = pw (|2 * K4| * MT) (-(1 / 2)) (3 / 2) x := by
            unfold pw; ring
        _ ≤ _ := le_rfl
    · rfl

/-! ### From the two-regime classes to `BumpProfile` -/

/-- A profile of the class `(M, α, β)` on `[3δ/2, ∞)` vanishing below `3δ/2` is a `BumpProfile (3/2) δ M α β K`
(`uct:bump-symbol`, `fct:bump-5`). -/
lemma SymW.toBumpProfile {δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ} (h : SymW (Ici (3 / 2 * δ)) (pw M α β) K B)
    (hM : 0 ≤ M) (hsup : ∀ x : ℝ, x < 3 / 2 * δ → B x = 0) : BumpProfile (3 / 2) δ M α β K B where
  smooth := by
    obtain ⟨U, hU, hSU, hBU⟩ := h.smooth
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 3 / 2 * δ ≤ x
    · exact (hBU.contDiffAt (hU.mem_nhds (hSU hx)))
    · have hev : B =ᶠ[nhds x] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (Iio_mem_nhds (not_le.mp hx)) fun y hy => hsup y hy
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  support := hsup
  near := fun k x hx hx1 => by
    have hxp : 0 < x := h.pos x hx
    have hb := h.bound k x hx
    have hk : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by rw [Real.rpow_neg hxp.le, Real.rpow_natCast]
    have e : pw M α β x = M * x ^ (-α) := by simp only [pw, hx1, ↓reduceIte]
    rw [e] at hb
    refine hb.trans (le_of_eq ?_)
    rw [show -α - (k : ℝ) = -α + -(k : ℝ) by ring, Real.rpow_add hxp, hk]
    ring
  far := fun k x hx1 => by
    by_cases hx : 3 / 2 * δ ≤ x
    · have hxp : 0 < x := h.pos x hx
      have hb := h.bound k x hx
      have hk : x ^ (-(k : ℝ)) = (x ^ k)⁻¹ := by rw [Real.rpow_neg hxp.le, Real.rpow_natCast]
      have e : pw M α β x = M * x ^ (-β) := by
        unfold pw
        by_cases h1 : x ≤ 1
        · have : x = 1 := le_antisymm h1 hx1
          subst this; simp
        · simp only [h1, ↓reduceIte]
      rw [e] at hb
      refine hb.trans (le_of_eq ?_)
      rw [show -β - (k : ℝ) = -β + -(k : ℝ) by ring, Real.rpow_add hxp, hk]
      ring
    · rw [iteratedDeriv_zero_of_support hsup k (not_le.mp hx)]
      simp only [abs_zero]
      have hxp : 0 < x := by linarith
      exact mul_nonneg (mul_nonneg (h.K_nonneg k) hM) (Real.rpow_nonneg hxp.le _)

/-! ### The bump `(fct:B-physical)` -/

/-- `η(L) = K₁ (c^{-2} L^{-2} + c^{-1})`. -/
noncomputable def physEta (c K1 x : ℝ) : ℝ := K1 * (c⁻¹ ^ 2 * x ^ (-2 : ℝ) + c⁻¹)

/-- The common physical bump `(fct:B-physical)`, as a function of `L`:
`B = n χ(L/3δ) γ(L̃) [(1 + η) O − (1 − η) F] + 2 K₄ n χ(L/3δ) (1 − χ(L/6δ)) τ₀⁴ I_fl`, with `T4 = τ₀⁴ I_fl`, `L̃ = L − s`. -/
noncomputable def physBump (χ : ℝ → ℝ) (n c δ s K1 K4 : ℝ) (O F T4 : ℝ → ℝ) (x : ℝ) : ℝ :=
  n * (χ (x / (3 * δ)) * physGamma c s x * ((1 + physEta c K1 x) * O x - (1 - physEta c K1 x) * F x)) +
    n * (2 * K4 * (χ (x / (3 * δ)) * ((1 - χ (x / (6 * δ))) * T4 x)))

/-- The constants of the whole bump: `Σ` of the four pieces. -/
noncomputable def KpTot (Kχ KΦ KR KT : ℕ → ℝ) (r : ℕ) : ℝ :=
  KpDiff Kχ KΦ KR r + KpMar1 Kχ KΦ KR r + KpMar2 Kχ KΦ KR r + KpTr Kχ KT r

/-- **`fct:bump-sym-check`, assembled** (Lemma FCT.7b, for the bump `(fct:B-physical)` of `H_*` and of `H_CE`):
under the symbol-class inputs `F ∈ (M_Φ, 3/2, 3/2)`, `R − 1 ∈ (M_R, -1, 0)`, `τ₀⁴ I_fl ∈ (M_T, -1/2, 3/2)` on `[3δ/2, 6δ]`
(`O = F R`), the bump `B` is a `BumpProfile (3/2) δ (|n| M_tot) (7/2) (3/2) K`, with `K = KpTot` independent of `c`: it is the sum of
the four pieces of `physBump_pieces` with `(1/2, 3/2)`, `(7/2, 7/2)`, `(3/2, 3/2)`, `(-1/2, 3/2)`, each weakened to `(7/2, 3/2)`. -/
theorem physBump_profile {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Kχ : ℕ → ℝ} (hKχ : ∀ (r : ℕ) (s : ℝ), |iteratedDeriv r χ s| ≤ Kχ r)
    {KΦ KR KT : ℕ → ℝ} {n c δ s K1 K4 MΦ MR MT : ℝ} {F R T4 : ℝ → ℝ}
    (hδ : 0 < δ) (hs : |s| ≤ 3 / 2 * δ / 2) (hsmall : (5 * π ^ 2 / 96) * c⁻¹ ^ 2 * (3 / 2 * δ) ^ (-3 : ℝ) ≤ 1)
    (hMΦ : 0 ≤ MΦ) (hMR : 0 ≤ MR) (hMT : 0 ≤ MT)
    (hF : SymW (Ici (3 / 2 * δ)) (pw MΦ (3 / 2) (3 / 2)) KΦ F)
    (hR : SymW (Ici (3 / 2 * δ)) (pw MR (-1) 0) KR (fun x => R x - 1))
    (hT : SymW (Icc (3 / 2 * δ) (6 * δ)) (pw MT (-(1 / 2)) (3 / 2)) KT T4) :
    BumpProfile (3 / 2) δ
      (|n| * (MΦ * MR + |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) + |K1 * c⁻¹| * (MΦ * (MR + 2)) + |2 * K4| * MT))
      (7 / 2) (3 / 2) (KpTot Kχ KΦ KR KT) (physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4) := by
  obtain ⟨p1, p2, p3, p4⟩ := physBump_pieces hχ hKχ (K1 := K1) (K4 := K4) (c := c) (s := s) (MΦ := MΦ) (αΦ := 3 / 2)
    (βΦ := 3 / 2) (MR := MR) (MT := MT) hδ hs hsmall hMR hMT hF hR hT
  have hx0 : 0 < 3 / 2 * δ := by positivity
  have hxpos : ∀ x ∈ Ici (3 / 2 * δ), 0 < x := fun x hx => lt_of_lt_of_le hx0 hx
  set m1 := MΦ * MR with hm1
  set m2 := |K1 * c⁻¹ ^ 2| * (MΦ * (MR + 2)) with hm2
  set m3 := |K1 * c⁻¹| * (MΦ * (MR + 2)) with hm3
  set m4 := |2 * K4| * MT with hm4
  have n1 : 0 ≤ m1 := mul_nonneg hMΦ hMR
  have n2 : 0 ≤ m2 := mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith))
  have n3 : 0 ≤ m3 := mul_nonneg (abs_nonneg _) (mul_nonneg hMΦ (by linarith))
  have n4 : 0 ≤ m4 := mul_nonneg (abs_nonneg _) hMT
  have q1 := p1.of_le (w' := pw (m1 + m2 + m3 + m4) (7 / 2) (3 / 2)) (fun x hx => pw_le_pw (by linarith) n1
    (by norm_num) (by norm_num) (hxpos x hx)) (fun _ => le_rfl)
  have q2 := p2.of_le (w' := pw (m1 + m2 + m3 + m4) (7 / 2) (3 / 2)) (fun x hx => pw_le_pw (by linarith) n2
    (by norm_num) (by norm_num) (hxpos x hx)) (fun _ => le_rfl)
  have q3 := p3.of_le (w' := pw (m1 + m2 + m3 + m4) (7 / 2) (3 / 2)) (fun x hx => pw_le_pw (by linarith) n3
    (by norm_num) (by norm_num) (hxpos x hx)) (fun _ => le_rfl)
  have q4 := p4.of_le (w' := pw (m1 + m2 + m3 + m4) (7 / 2) (3 / 2)) (fun x hx => pw_le_pw (by linarith) n4
    (by norm_num) (by norm_num) (hxpos x hx)) (fun _ => le_rfl)
  have hsum := ((q1.add q2).add q3).add q4
  have hn := hsum.smul n
  have hfin := (hn.of_le (w' := pw (|n| * (m1 + m2 + m3 + m4)) (7 / 2) (3 / 2))
    (fun x hx => le_of_eq (pw_scale _ _ _ _ _)) (fun r => le_rfl)).congr (U := univ) isOpen_univ (subset_univ _)
    (g := physBump χ n c δ s K1 K4 (fun x => F x * R x) F T4) fun x _ => by
      simp only [physBump, physEta]; ring
  refine hfin.toBumpProfile (mul_nonneg (abs_nonneg n) (by linarith)) ?_
  intro x hx
  have hx3 : x / (3 * δ) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  simp only [physBump, hχ.zero _ hx3]; ring

/-- info: 'FormalResearch.SignUncertainty.FctSym.physBump_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_pieces

/-- info: 'FormalResearch.SignUncertainty.FctSym.physBump_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physBump_profile

end FormalResearch.SignUncertainty.FctSym
