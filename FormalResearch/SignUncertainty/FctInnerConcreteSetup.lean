/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerJ0
public import FormalResearch.SignUncertainty.FctInnerFactorsA
public import FormalResearch.SignUncertainty.FctInnerFactorsB

/-!
# Concrete phase-box setup and family `concreteInnerFamily` for `fct:inner-symbols` (b3)–(b4)

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (b3)–(b4):
instantiates `FctInnerFamily` (`concreteInnerFamily K4 ε`) from the concrete CFU phase box
(`concretePhaseBox_exist`, `FctInnerPhase`) and proves:
* `concreteInnerB3`: `FctInnerB3 (concreteInnerFamily K4 ε)` (`δμ ∈ 𝒮^{10}(C c^{-4/3})`), combining
  `fctInner_J1_sub_J0_sym`, `fctInner_J0_sub_one_sym`, `fctInner_T4_sym`, `fctInner_v1_sym`,
  `fctInner_V_sq_sub_V0_sym`, `fctInner_binet_sym`, and `fctInner_phiKillDivM_sym`;
* `concreteInnerB4`: `FctInnerB4 (concreteInnerFamily K4 ε)` (`e_B ∈ 𝒮^{11}(C c^{-1/2})`,
  `e_A ∈ 𝒮^3(C c^{-2/3})`), combining `fctInner_V_sub_tauStar_sym`, `fctInner_theta1_sym`,
  `fctInner_V_sub_VA_sym`, and `fctInner_phiKillDivM_sym`;
* `concrete_eB_id`, `concrete_eA_id`: the defining `(b4)` identities for `ω₁(T)` and `ω₂(T)/û_L`.

Class: proved, unconditional.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctCompD
open FormalResearch.SignUncertainty.FctPhiKill
open FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

local notation "τs" => ((12 / π ^ 2) ^ (1 / 3 : ℝ))

/-! ### 1. Canonical CFU box selection from `concretePhaseBox_exist` -/

theorem pbTuple_exist :
    ∃ x : ℝ × ℝ × ℝ × ℝ × ℝ,
      0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 < x.2.2.2.1 ∧ 0 < x.2.2.2.2 ∧ x.2.2.2.2 ≤ 1 / 20 ∧
      ∀ {K4 ε c : ℝ}, 1 ≤ K4 → (ε = 1 ∨ ε = -1) → 0 < c →
        let τ₁ := c ^ (-(1 / 4 : ℝ))
        τ₁ ≤ x.2.2.2.2 → K4 * τ₁ ^ 2 ≤ 1 →
        ∃ (p : CfuTheta × ChartSetup (ℝ × ℝ × ℝ)),
          let T := p.1
          let S := p.2
          T.M = x.1 ∧ T.mt = concreteMt ∧ T.θt = concreteThetaT ε ∧
          S.Ω = OmT τ₁ ∧ S.ℓ = (fun q : ℝ × ℝ × ℝ => q.1) ∧ S.r = T.r τ₁ K4 ∧
          S.ε = x.2.2.1 * τ₁ ^ 2 ∧ S.cV = x.2.1 ∧
          FctPhaseBox (concretePhiTilde K4 ε c) (concretePhaseDom x.2.2.2.1 ε c) (concreteTau0 ε c S) ∧
          (∀ p0 ∈ concretePhaseDom x.2.2.2.1 ε c,
            let q := (concreteEll1 ε c p0.1, (1 : ℝ), p0.2)
            concreteTau0 ε c S p0 < 2 * τ₁ ∧
            S.A q ∈ Ioo (0 : ℝ) 2.9 ∧
            fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p0 = τ₁ ^ 2 * S.A q ∧
            fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p0 (1, 0) = S.V (q, S.A q) ∧
            fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p0 (0, 1) =
              c⁻¹ * fctThetaD (vAlpha 1 τ₁) (concreteTau0 ε c S p0) /
                Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p0)) ∧
          (∀ {lam L1 α x : ℝ}, 0 ≤ x → x ≤ 2.4 →
            τ₁ ^ 3 * (x * ((L1 - ctTheta1 ε / c) / τ₁ ^ 2 - π ^ 2 / 36 * x ^ 2 +
              T.r τ₁ K4 (((L1 - ctTheta1 ε / c) / τ₁ ^ 2, lam, α), x ^ 2))) =
              concretePhiLambda K4 ε c lam (τ₁ * x) L1 α) := by
  obtain ⟨M_cfu, cV, C0, ellMin, τ_lim, hM0, hcV, hC0, hellMin, hτ0, hτle, hmain⟩ :=
    concretePhaseBox_exist
  refine ⟨(M_cfu, cV, C0, ellMin, τ_lim), hM0, hcV, hC0, hellMin, hτ0, hτle, ?_⟩
  intro K4 ε c hK4 hε hc τ₁ hτ1 hK4t
  obtain ⟨T, _, _, _, _, S, hTM, hTmt, hTθt, hSΩ, hSℓ, hSr, hSε, hScV, _, _, _, _, hTid, hbox, hpb1⟩ :=
    hmain hK4 hε hc hτ1 hK4t
  exact ⟨(T, S), hTM, hTmt, hTθt, hSΩ, hSℓ, hSr, hSε, hScV, hbox, hpb1, hTid⟩

noncomputable abbrev pbTuple : ℝ × ℝ × ℝ × ℝ × ℝ := pbTuple_exist.choose

noncomputable abbrev pbM : ℝ := pbTuple.1
noncomputable abbrev pbcV : ℝ := pbTuple.2.1
noncomputable abbrev pbC0 : ℝ := pbTuple.2.2.1
noncomputable abbrev pbellMin : ℝ := pbTuple.2.2.2.1
noncomputable abbrev pbTauLim : ℝ := pbTuple.2.2.2.2

lemma pbM_nonneg : 0 ≤ pbM := pbTuple_exist.choose_spec.1
lemma pbcV_nonneg : 0 ≤ pbcV := pbTuple_exist.choose_spec.2.1
lemma pbC0_nonneg : 0 ≤ pbC0 := pbTuple_exist.choose_spec.2.2.1
lemma pbellMin_pos : 0 < pbellMin := pbTuple_exist.choose_spec.2.2.2.1
lemma pbTauLim_pos : 0 < pbTauLim := pbTuple_exist.choose_spec.2.2.2.2.1
lemma pbTauLim_le : pbTauLim ≤ 1 / 20 := pbTuple_exist.choose_spec.2.2.2.2.2.1

/-- Valid regime `(K₄, ε, c)` for `concretePhaseBox_exist`. -/
def concreteBoxValid (K4 ε c : ℝ) : Prop :=
  1 ≤ K4 ∧ (ε = 1 ∨ ε = -1) ∧ 0 < c ∧ c ^ (-(1 / 4 : ℝ)) ≤ pbTauLim ∧ K4 * (c ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1

lemma concreteBox_witness_nonempty : Nonempty CfuTheta ∧ Nonempty (ChartSetup (ℝ × ℝ × ℝ)) := by
  let c0 : ℝ := pbTauLim ^ (-4 : ℝ)
  have hc0_pos : 0 < c0 := Real.rpow_pos_of_pos pbTauLim_pos _
  have hτ0 : c0 ^ (-(1 / 4 : ℝ)) = pbTauLim := by
    dsimp only [c0]
    rw [← Real.rpow_mul pbTauLim_pos.le]; norm_num
  have hτ_sq : 1 * (c0 ^ (-(1 / 4 : ℝ))) ^ 2 ≤ 1 := by
    rw [one_mul, hτ0]; nlinarith [pbTauLim_pos, pbTauLim_le]
  obtain ⟨⟨T, S⟩, _⟩ :=
    pbTuple_exist.choose_spec.2.2.2.2.2.2
      (K4 := 1) (ε := 1) (c := c0) le_rfl (Or.inl rfl) hc0_pos hτ0.le hτ_sq
  exact ⟨⟨T⟩, ⟨S⟩⟩

noncomputable def pbBoxPair (K4 ε c : ℝ) : CfuTheta × ChartSetup (ℝ × ℝ × ℝ) := by
  classical
  exact if h : concreteBoxValid K4 ε c then
    (pbTuple_exist.choose_spec.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose
  else
    (concreteBox_witness_nonempty.1.some, concreteBox_witness_nonempty.2.some)

/-- Canonical `CfuTheta` at `(K4, ε, c)` when `concreteBoxValid K4 ε c`. -/
noncomputable def concreteBoxT (K4 ε c : ℝ) : CfuTheta := (pbBoxPair K4 ε c).1

/-- Canonical `ChartSetup` at `(K4, ε, c)` when `concreteBoxValid K4 ε c`. -/
noncomputable def concreteBoxS (K4 ε c : ℝ) : ChartSetup (ℝ × ℝ × ℝ) := (pbBoxPair K4 ε c).2

lemma concreteBox_spec {K4 ε c : ℝ} (h : concreteBoxValid K4 ε c) :
    let T := concreteBoxT K4 ε c
    let S := concreteBoxS K4 ε c
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    T.M = pbM ∧ T.mt = concreteMt ∧ T.θt = concreteThetaT ε ∧
    S.Ω = OmT τ₁ ∧ S.ℓ = (fun p : ℝ × ℝ × ℝ => p.1) ∧ S.r = T.r τ₁ K4 ∧
    S.ε = pbC0 * τ₁ ^ 2 ∧ S.cV = pbcV ∧
    FctPhaseBox (concretePhiTilde K4 ε c) (concretePhaseDom pbellMin ε c) (concreteTau0 ε c S) ∧
    (∀ p ∈ concretePhaseDom pbellMin ε c,
      let q := (concreteEll1 ε c p.1, (1 : ℝ), p.2)
      concreteTau0 ε c S p < 2 * τ₁ ∧
      S.A q ∈ Ioo (0 : ℝ) 2.9 ∧
      fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p = τ₁ ^ 2 * S.A q ∧
      fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (1, 0) = S.V (q, S.A q) ∧
      fderiv ℝ (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S)) p (0, 1) =
        c⁻¹ * fctThetaD (vAlpha 1 τ₁) (concreteTau0 ε c S p) /
          Real.sqrt (fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) p)) := by
  classical
  have hpair : pbBoxPair K4 ε c =
      (pbTuple_exist.choose_spec.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose := by
    unfold pbBoxPair; simp only [h, ↓reduceDIte]
  have hspec :=
    (pbTuple_exist.choose_spec.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose_spec
  dsimp only
  unfold concreteBoxT concreteBoxS
  rw [hpair]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2.1,
    hspec.2.2.2.2.2.2.1, hspec.2.2.2.2.2.2.2.1, hspec.2.2.2.2.2.2.2.2.1, hspec.2.2.2.2.2.2.2.2.2.1⟩

lemma concreteBox_phi_id {K4 ε c : ℝ} (h : concreteBoxValid K4 ε c) :
    let T := concreteBoxT K4 ε c
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    ∀ {lam L1 α x : ℝ}, 0 ≤ x → x ≤ 2.4 →
      τ₁ ^ 3 * (x * ((L1 - ctTheta1 ε / c) / τ₁ ^ 2 - π ^ 2 / 36 * x ^ 2 +
        T.r τ₁ K4 (((L1 - ctTheta1 ε / c) / τ₁ ^ 2, lam, α), x ^ 2))) =
        concretePhiLambda K4 ε c lam (τ₁ * x) L1 α := by
  classical
  have hpair : pbBoxPair K4 ε c =
      (pbTuple_exist.choose_spec.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose := by
    unfold pbBoxPair; simp only [h, ↓reduceDIte]
  have hspec :=
    (pbTuple_exist.choose_spec.2.2.2.2.2.2 h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2).choose_spec
  dsimp only
  unfold concreteBoxT
  rw [hpair]
  intro lam L1 α x hx0 hx24
  exact hspec.2.2.2.2.2.2.2.2.2.2 hx0 hx24

/-! ### 2. Concrete `FctInnerFamily` matching `(fct:inner-symbols)` (b3)–(b4) -/

/-- Extended `V` function `Y ↦ S.V ((ell1, 1, α), clampY Y)` on `[0, 3.6]` agreeing with `S.V` on `[0, 3.5]`. -/
noncomputable def concreteInnerV (K4 ε c L1 α Y : ℝ) : ℝ :=
  (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), clampY Y)

/-- Concrete inner-amplitude family of Lemma `fct:inner-symbols` (b3)–(b4). -/
noncomputable def concreteInnerFamily (K4 ε : ℝ) : FctInnerFamily where
  adm c L1 α :=
    concreteBoxValid K4 ε c ∧
    (L1, α) ∈ concretePhaseDom pbellMin ε c ∧
    |-fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c (concreteBoxS K4 ε c)) (L1, α) -
      FormalResearch.Special.airyZero 1| ≤ c ^ (-(7 / 6 : ℝ)) ∧
    |α| ≤ c ^ (-(1 / 2 : ℝ))
  mu c L1 α u :=
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let T := fctInnerT c (concreteInnerV K4 ε c L1 α) u
    ((Jfun S.V fctH (τ₁ ^ 2) (q, fctInnerY c u) : ℝ) : ℂ) *
      Complex.exp (-((K4 * T ^ 4 : ℝ) : ℂ) +
        ((v1 StripKernelChoice.star K4 c τ₁ T : ℝ) : ℂ) +
        ((α * T ^ 2 : ℝ) : ℂ) +
        FormalResearch.Asymptotics.binetDiff c (Complex.I * (T : ℂ))) *
      (1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) T)
  c2 c L1 α :=
    (2 : ℝ) ^ (-(4 / 3 : ℝ)) * ((concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α), 0)) ^ 2
  eB c L1 α u :=
    let V := concreteInnerV K4 ε c L1 α
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let T := fctInnerT c V u
    (((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (V (fctInnerY c u) ^ 2 - τs ^ 2) * u ^ 2 : ℝ) : ℂ) +
      Complex.I * ((c ^ (2 / 3 : ℝ) * fctThetaD (vAlpha 1 τ₁) T : ℝ) : ℂ)
  eA c L1 α u :=
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let V := concreteInnerV K4 ε c L1 α
    let T := fctInnerT c V u
    let uL := -fctKappa c * S.V (q, S.A q)
    (-(Complex.I * (u : ℂ)) * (((V (fctInnerY c u) - S.V (q, S.A q)) / S.V (q, S.A q) : ℝ) : ℂ)) -
      phiKillDivM (c ^ (-(1 / 12 : ℝ))) T /
        ((1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) T) * (uL : ℂ))

lemma concrete_eB_id {K4 ε c L1 α u : ℝ} (hc : 0 < c) :
    ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
      (((fctInnerT c (concreteInnerV K4 ε c L1 α) u) ^ 2 : ℝ) +
        Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) (fctInnerT c (concreteInnerV K4 ε c L1 α) u) : ℝ) : ℂ)) =
    (((2 : ℝ) ^ (-(4 / 3 : ℝ)) * τs ^ 2 * u ^ 2 : ℝ) : ℂ) + (concreteInnerFamily K4 ε).eB c L1 α u := by
  set V := concreteInnerV K4 ε c L1 α
  set T := fctInnerT c V u
  have hT2 : c ^ (2 / 3 : ℝ) * T ^ 2 = (2 : ℝ) ^ (-(4 / 3 : ℝ)) * (V (fctInnerY c u)) ^ 2 * u ^ 2 := by
    have hT_eq : T = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V (fctInnerY c u) := rfl
    have hc23 : c ^ (2 / 3 : ℝ) * (c ^ (-(1 / 3 : ℝ))) ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_add hc]; norm_num
    have h243 : ((2 : ℝ) ^ (-(2 / 3 : ℝ))) ^ 2 = (2 : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [hT_eq, mul_pow, mul_pow, mul_pow, h243]
    calc c ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (c ^ (-(1 / 3 : ℝ))) ^ 2 * u ^ 2 * V (fctInnerY c u) ^ 2)
        = (c ^ (2 / 3 : ℝ) * (c ^ (-(1 / 3 : ℝ))) ^ 2) * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * V (fctInnerY c u) ^ 2 * u ^ 2) := by ring
      _ = _ := by rw [hc23, one_mul]
  dsimp only [concreteInnerFamily]
  have hr : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((T ^ 2 : ℝ) : ℂ) =
      (((2 : ℝ) ^ (-(4 / 3 : ℝ)) * τs ^ 2 * u ^ 2 : ℝ) : ℂ) +
        (((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (V (fctInnerY c u) ^ 2 - τs ^ 2) * u ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hT2]; push_cast; ring
  calc ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        (((T ^ 2 : ℝ) : ℂ) + Complex.I * ((fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) T : ℝ) : ℂ))
      = ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * ((T ^ 2 : ℝ) : ℂ) +
          Complex.I * (((c ^ (2 / 3 : ℝ) * fctThetaD (vAlpha 1 (c ^ (-(1 / 4 : ℝ)))) T : ℝ) : ℂ)) := by
            push_cast; ring
    _ = _ := by rw [hr]; ring

lemma concrete_eA_id {K4 ε c L1 α u : ℝ} (hc : 0 < c)
    (hVA : (concreteBoxS K4 ε c).V ((concreteEll1 ε c L1, (1 : ℝ), α),
      (concreteBoxS K4 ε c).A (concreteEll1 ε c L1, (1 : ℝ), α)) ≠ 0) :
    let V := concreteInnerV K4 ε c L1 α
    let T := fctInnerT c V u
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let uL := -fctKappa c * S.V (q, S.A q)
    let rhoK := phiKillDivM (c ^ (-(1 / 12 : ℝ))) T / (1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) T)
    (Complex.I * ((c * T : ℝ) : ℂ) - rhoK) / (uL : ℂ) =
      -(Complex.I * (u : ℂ)) + (concreteInnerFamily K4 ε).eA c L1 α u := by
  intro V T S q uL rhoK
  have hT_eq : T = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V (fctInnerY c u) := rfl
  have hc_eq : c * c ^ (-(1 / 3 : ℝ)) = c ^ (2 / 3 : ℝ) := by
    calc c * c ^ (-(1 / 3 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c ^ (2 / 3 : ℝ) := by rw [← Real.rpow_add hc]; norm_num
  have hcT : c * T / uL = -u * (V (fctInnerY c u) / S.V (q, S.A q)) := by
    have hκ_eq : fctKappa c = (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) := rfl
    have h2ne : (2 : ℝ) ^ (-(2 / 3 : ℝ)) ≠ 0 := by positivity
    have hc23ne : c ^ (2 / 3 : ℝ) ≠ 0 := by positivity
    dsimp only [uL]
    rw [hT_eq, hκ_eq]
    calc c * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) * u * V (fctInnerY c u)) /
          (-((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * S.V (q, S.A q))
        = ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (c * c ^ (-(1 / 3 : ℝ))) * (u * V (fctInnerY c u))) /
            (-((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * S.V (q, S.A q)) := by ring
      _ = ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * (u * V (fctInnerY c u))) /
            (-((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * S.V (q, S.A q)) := by rw [hc_eq]
      _ = -u * (V (fctInnerY c u) / S.V (q, S.A q)) := by field_simp [h2ne, hc23ne, hVA]
  have h1 : Complex.I * ((c * T : ℝ) : ℂ) / (uL : ℂ) =
      -(Complex.I * (u : ℂ)) -
        Complex.I * (u : ℂ) * (((V (fctInnerY c u) - S.V (q, S.A q)) / S.V (q, S.A q) : ℝ) : ℂ) := by
    have hr : (c * T : ℝ) / uL = -u - u * ((V (fctInnerY c u) - S.V (q, S.A q)) / S.V (q, S.A q)) := by
      rw [hcT, sub_div, div_self hVA]; ring
    have heqC : Complex.I * ((c * T : ℝ) : ℂ) / (uL : ℂ) = Complex.I * (((c * T / uL : ℝ) : ℂ)) := by
      push_cast; ring
    rw [heqC, hr]
    push_cast; ring
  have h2 : rhoK / (uL : ℂ) =
      phiKillDivM (c ^ (-(1 / 12 : ℝ))) T /
        ((1 - (L1 : ℂ) * phiKillDivM (c ^ (-(1 / 12 : ℝ))) T) * (uL : ℂ)) := by
    dsimp only [rhoK]; rw [div_div]
  dsimp only [concreteInnerFamily]
  rw [sub_div, h1, h2]
  ring

/-! ### 3. Symbol helpers & admissible-box bounds -/

lemma one_add_Uc_rpow_le {c : ℝ} (hc : 1 ≤ c) (p : ℝ) (hp : 0 ≤ p) :
    (1 + fctUc c) ^ p ≤ 4 ^ p * c ^ (p / 12) := by
  have hc0 : 0 < c := by linarith
  have h1 : 1 + fctUc c ≤ 4 * c ^ ((1 : ℝ) / 12) := one_add_fctUc_le hc
  calc (1 + fctUc c) ^ p ≤ (4 * c ^ ((1 : ℝ) / 12)) ^ p :=
        Real.rpow_le_rpow (by linarith [fctUc_pos hc0]) h1 hp
    _ = 4 ^ p * (c ^ ((1 : ℝ) / 12)) ^ p := Real.mul_rpow (by norm_num) (by positivity)
    _ = 4 ^ p * c ^ (p / 12) := by rw [← Real.rpow_mul hc0.le]; congr 2; ring

lemma concrete_u_sym {c : ℝ} (hc0 : 0 < c) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 1 1 (fun u => (u : ℂ)) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  refine FctSymClsOn.ofReal_cast hDu contDiffOn_id fun r _ u hu => ?_
  rw [show (fun u : ℝ => u) = id from rfl, iteratedDerivWithin_eq_iteratedDeriv hDu contDiffAt_id hu]
  have hid : (id : ℝ → ℝ) = fun x : ℝ => x := rfl
  rw [hid]
  have h1u : 1 ≤ 1 + u := by linarith [hu.1]
  rcases (by omega : r = 0 ∨ r = 1 ∨ 2 ≤ r) with rfl | rfl | hr2
  · rw [iteratedDeriv_zero, abs_of_nonneg hu.1, Nat.cast_zero, sub_zero, Real.rpow_one, one_mul]
    linarith [hu.1]
  · rw [iteratedDeriv_one, deriv_id'', abs_one, Nat.cast_one, sub_self, Real.rpow_zero, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
    have h2 : ∀ n : ℕ, ∀ x : ℝ, iteratedDeriv (n + 2) (fun x : ℝ => x) x = 0 := by
      intro n
      induction n with
      | zero => intro x; rw [zero_add, iteratedDeriv_succ, iteratedDeriv_one]; simp
      | succ n ih =>
        intro x
        rw [show n + 1 + 2 = (n + 2) + 1 by omega, iteratedDeriv_succ]
        have hfn : iteratedDeriv (n + 2) (fun x : ℝ => x) = fun _ => (0 : ℝ) := funext ih
        rw [hfn]; simp
    rw [h2 m u, abs_zero]
    positivity

lemma concrete_u_sq_sym {c : ℝ} (hc0 : 0 < c) :
    FctSymClsOn (Icc 0 (fctUc c)) 8 2 2 (fun u => ((u ^ 2 : ℝ) : ℂ)) := by
  have hUc0 : 0 < fctUc c := fctUc_pos hc0
  have hDu := uniqueDiffOn_Icc hUc0
  refine FctSymClsOn.ofReal_cast hDu (contDiffOn_id.pow 2) fun r _ u hu => ?_
  rw [show (fun u : ℝ => u ^ 2) = (fun y => id y ^ 2) from rfl,
    iteratedDerivWithin_eq_iteratedDeriv hDu (contDiffAt_id.pow 2) hu]
  have hsq : (fun y : ℝ => id y ^ 2) = fun x : ℝ => x ^ 2 := rfl
  rw [hsq]
  have hu0 : 0 ≤ u := hu.1
  have h1u : 1 ≤ 1 + u := by linarith only [hu0]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r) with rfl | rfl | rfl | hr3
  · rw [iteratedDeriv_zero, abs_of_nonneg (sq_nonneg u), Nat.cast_zero, sub_zero, Real.rpow_two]
    nlinarith only [hu0]
  · have hd1 : deriv (fun x : ℝ => x ^ 2) u = 2 * u := by
      simp
    rw [iteratedDeriv_one, hd1, abs_mul, abs_of_pos zero_lt_two, abs_of_nonneg hu0,
      Nat.cast_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    linarith only [hu0]
  · have hd2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) u = 2 := by
      have hfn : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
        ext x; simp
      rw [iteratedDeriv_succ, iteratedDeriv_one, hfn]
      simp
    rw [hd2, abs_of_pos zero_lt_two, Nat.cast_ofNat, sub_self, Real.rpow_zero, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m, r = m + 3 := ⟨r - 3, by omega⟩
    have h2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) = fun _ => (2 : ℝ) := by
      ext x
      have hfn : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
        ext z; simp
      rw [iteratedDeriv_succ, iteratedDeriv_one, hfn]
      simp
    have h3 : ∀ n : ℕ, ∀ x : ℝ, iteratedDeriv (n + 3) (fun x : ℝ => x ^ 2) x = 0 := by
      intro n
      induction n with
      | zero => intro x; rw [zero_add, iteratedDeriv_succ, h2]; simp
      | succ n ih =>
        intro x
        rw [show n + 1 + 3 = (n + 3) + 1 by omega, iteratedDeriv_succ]
        have hfn : iteratedDeriv (n + 3) (fun x : ℝ => x ^ 2) = fun _ => (0 : ℝ) := funext ih
        rw [hfn]; simp
    rw [h3 m u, abs_zero]
    positivity

lemma abs_ell1_le_of_A {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : ChartSetup P} {p : P} (hp : p ∈ S.Ω) (hr0 : S.r (p, 0) = 0) (h15 : 15 * S.ε ≤ 1 / 2)
    (hSA_nn : 0 ≤ S.A p) {b : ℝ} (hb : S.A p ≤ b) :
    |S.ℓ p| ≤ 2 * b := by
  have hO : IsOpen (S.Ω ×ˢ Ioo (-1 : ℝ) 6) := S.hΩ.prod isOpen_Ioo
  have hρ_bd : ∀ z ∈ Ioo (-1 : ℝ) 6, |rhoF S.r (p, z)| ≤ 1 / 2 * |z| := by
    intro z hz
    have hp_emb : ContDiffOn ℝ 18 (fun w : ℝ => (p, w)) (Ioo (-1 : ℝ) 6) := by fun_prop
    have hr_w : ContDiffOn ℝ 18 (fun w => S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
      S.hr.1.comp hp_emb fun w hw => ⟨hp, hw⟩
    have h17 := (S.hr.succ_fderiv hO).clm_apply_const hO.uniqueDiffOn ((0 : P), (1 : ℝ))
    have hfd_w : ContDiffOn ℝ 17 (fun w => fderiv ℝ S.r (p, w) (0, 1)) (Ioo (-1 : ℝ) 6) :=
      h17.1.comp (hp_emb.of_le (by norm_num : (17 : WithTop ℕ∞) ≤ 18)) fun w hw => ⟨hp, hw⟩
    have hrho_cd : ContDiffOn ℝ 1 (fun w => rhoF S.r (p, w)) (Ioo (-1 : ℝ) 6) :=
      ((hr_w.of_le (by norm_num)).add
        (contDiffOn_const.mul (contDiffOn_id.mul (hfd_w.of_le (by norm_num))))).congr fun _ _ => rfl
    have hderiv_bd : ∀ w ∈ Ioo (-1 : ℝ) 6, |deriv (fun t => rhoF S.r (p, t)) w| ≤ 1 / 2 := by
      intro w hw
      have hq : (p, w) ∈ S.Ω ×ˢ Ioo (-1 : ℝ) 6 := ⟨hp, hw⟩
      have hdr : HasDerivAt (fun t => S.r (p, t)) (fderiv ℝ S.r (p, w) (0, 1)) w :=
        (((S.hr.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt w
          (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
      have hd2 : HasDerivAt (fun t => fderiv ℝ S.r (p, t) (0, 1))
          (fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)) w :=
        (((h17.1.contDiffAt (hO.mem_nhds hq)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt w
          (by simpa using (hasDerivAt_const w p).prodMk (hasDerivAt_id w))
      have htot : HasDerivAt (fun t => rhoF S.r (p, t))
          (fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
            w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))) w :=
        (hdr.add (((hasDerivAt_id w).mul hd2).const_mul 2)).congr_of_eventuallyEq
          (Eventually.of_forall fun t => by simp [rhoF])
      rw [htot.deriv]
      have hb1 : |fderiv ℝ S.r (p, w) (0, 1)| ≤ S.ε := by
        have hbd := S.hr.2 1 (by norm_num) (p, w) hq
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
        calc |fderiv ℝ S.r (p, w) (0, 1)| = ‖fderiv ℝ S.r (p, w) (0, 1)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ S.r (p, w)‖ * ‖((0 : P), (1 : ℝ))‖ := (fderiv ℝ S.r _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul hbd (by simp [Prod.norm_def]) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hb2 : |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)| ≤ S.ε := by
        have hbd := h17.2 1 (by norm_num) (p, w) hq
        rw [norm_iteratedFDerivWithin_one _ (hO.uniqueDiffOn _ hq), fderivWithin_of_isOpen hO hq] at hbd
        have hbd' : ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ ≤ S.ε :=
          hbd.trans (by simp [Prod.norm_def])
        calc |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)|
            = ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)‖ := Real.norm_eq_abs _
          _ ≤ ‖fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w)‖ * ‖((0 : P), (1 : ℝ))‖ :=
              (fderiv ℝ _ _).le_opNorm _
          _ ≤ S.ε * 1 := mul_le_mul hbd' (by simp [Prod.norm_def]) (norm_nonneg _) S.hε
          _ = S.ε := mul_one _
      have hw6 : |w| ≤ 6 := by rw [abs_le]; constructor <;> linarith only [hw.1, hw.2]
      calc |fderiv ℝ S.r (p, w) (0, 1) + 2 * (1 * fderiv ℝ S.r (p, w) (0, 1) +
              w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))|
          ≤ |fderiv ℝ S.r (p, w) (0, 1)| + 2 * (|fderiv ℝ S.r (p, w) (0, 1)| +
              |w| * |fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)|) := by
            have hmain := abs_add_le (fderiv ℝ S.r (p, w) (0, 1))
              (2 * (1 * fderiv ℝ S.r (p, w) (0, 1) + w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1)))
            have h2 := abs_add_le (1 * fderiv ℝ S.r (p, w) (0, 1))
              (w * fderiv ℝ (fun x => fderiv ℝ S.r x (0, 1)) (p, w) (0, 1))
            simp only [one_mul] at hmain h2 ⊢
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hmain
            rw [abs_mul] at h2
            linarith only [hmain, h2]
        _ ≤ S.ε + 2 * (S.ε + 6 * S.ε) := by gcongr
        _ = 15 * S.ε := by ring
        _ ≤ 1 / 2 := h15
    have hmv := (convex_Ioo (-1 : ℝ) 6).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hrho_cd.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num))
      (fun x hx => show ‖deriv (fun t => rhoF S.r (p, t)) x‖ ≤ 1 / 2 by
        rw [Real.norm_eq_abs]; exact hderiv_bd x hx)
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 6 by norm_num) hz
    have hrho0 : rhoF S.r (p, 0) = 0 := by simp [rhoF, hr0]
    simpa [hrho0, Real.norm_eq_abs] using hmv
  obtain ⟨hB_mem, hB_eq⟩ := S.out.2.1 p hp
  have hd_pos : 0 < S.d p := (S.out.2.2.2.1 p hp).1
  have hB_nn : 0 ≤ S.B p := by
    have hA_eq : S.A p = S.d p ^ 2 * S.B p := rfl
    have hsq_pos : 0 < S.d p ^ 2 := sq_pos_of_pos hd_pos
    have : S.B p = S.A p / S.d p ^ 2 := by rw [hA_eq]; field_simp [hsq_pos.ne']
    rw [this]; positivity
  have hd_bd := S.d_dev hp
  have hd_lo : (92 / 100 : ℝ) ≤ S.d p := by linarith only [abs_le.mp hd_bd |>.1, dStar_bounds.1, S.hcd]
  have hB_le : S.B p ≤ 100 / 84 * b := by
    have hsq : (84 / 100 : ℝ) ≤ S.d p ^ 2 := by nlinarith only [hd_lo]
    have hA_eq : S.B p * S.d p ^ 2 = S.A p := by unfold ChartSetup.A; ring
    have h1 : S.B p * (84 / 100 : ℝ) ≤ b := by
      calc S.B p * (84 / 100 : ℝ) ≤ S.B p * S.d p ^ 2 := mul_le_mul_of_nonneg_left hsq hB_nn
        _ = S.A p := hA_eq
        _ ≤ b := hb
    linarith only [h1]
  have h12pi : π ^ 2 / 12 ≤ 1 := by
    have : π < (3.15 : ℝ) := Real.pi_lt_d2
    nlinarith only [this, Real.pi_pos]
  have hρ := hρ_bd (S.B p) hB_mem
  rw [abs_of_nonneg hB_nn] at hρ
  have hℓ : S.ℓ p = π ^ 2 / 12 * S.B p - rhoF S.r (p, S.B p) := by linarith only [hB_eq]
  rw [hℓ]
  calc |π ^ 2 / 12 * S.B p - rhoF S.r (p, S.B p)|
      ≤ |π ^ 2 / 12 * S.B p| + |rhoF S.r (p, S.B p)| := abs_sub _ _
    _ = π ^ 2 / 12 * S.B p + |rhoF S.r (p, S.B p)| := by
        rw [abs_of_nonneg (mul_nonneg (by positivity) hB_nn)]
    _ ≤ 1 * S.B p + 1 / 2 * S.B p := add_le_add (mul_le_mul_of_nonneg_right h12pi hB_nn) hρ
    _ ≤ 2 * b := by linarith only [hB_nn, hB_le]

noncomputable def pbC_ext : ℝ := fctVJets_of_chartV.choose

lemma pbC_ext_pos : 0 < pbC_ext := fctVJets_of_chartV.choose_spec.1

noncomputable def pbKV : ℝ := pbC_ext * ((Nat.factorial 16 : ℝ) * (pbcV * pbC0))

lemma pbKV_nonneg : 0 ≤ pbKV :=
  mul_nonneg pbC_ext_pos.le (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg pbcV_nonneg pbC0_nonneg))

lemma concrete_adm_facts {K4 ε c L1 α : ℝ}
    (hc : max 100 ((30 * pbC0 + 1) ^ 2) ≤ c)
    (hadm : (concreteInnerFamily K4 ε).adm c L1 α) :
    let S := concreteBoxS K4 ε c
    let q := (concreteEll1 ε c L1, (1 : ℝ), α)
    let τ₁ := c ^ (-(1 / 4 : ℝ))
    let V := concreteInnerV K4 ε c L1 α
    0 < c ∧ 100 ≤ c ∧ τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) ∧
    q ∈ S.Ω ∧ concreteEll1 ε c L1 ∈ Ioo (0 : ℝ) 2.55 ∧
    S.A q ∈ Ioo (0 : ℝ) 2.9 ∧ S.A q ≤ 4 * c ^ (-(1 / 6 : ℝ)) ∧
    |L1| ≤ (8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ)) ∧
    JC 16 Yint (fun y => S.V (q, y) - τs) ((Nat.factorial 16 : ℝ) * (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)))) ∧
    (FctVJets pbKV c V ∧ ∀ y ∈ Icc (0 : ℝ) 3.5, V y = S.V (q, y)) ∧
    |S.V (q, S.A q) - τs| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) ∧
    |V 0 - τs| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
  rcases hadm with ⟨hvalid, hpDom, hadm_u, _⟩
  have hc100 : 100 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith only [hc100]
  have hτ₁_pos : 0 < c ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hτ₁_sq : (c ^ (-(1 / 4 : ℝ))) ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  obtain ⟨_, _, _, hSΩ, hSℓ, hSr, hSε, hScV, _, hpb1⟩ := concreteBox_spec hvalid
  obtain ⟨_, hA_mem, hatil_eq, _, _⟩ := hpb1 (L1, α) hpDom
  set S := concreteBoxS K4 ε c
  set q := (concreteEll1 ε c L1, (1 : ℝ), α)
  set τ₁ := c ^ (-(1 / 4 : ℝ))
  have hqΩ : q ∈ S.Ω := by rw [hSΩ]; exact concreteEll1_mem_OmT hc0 pbellMin_pos.le hpDom
  have hell1 : concreteEll1 ε c L1 ∈ Ioo (0 : ℝ) 2.55 :=
    ⟨lt_trans (mul_pos pbellMin_pos (Real.rpow_pos_of_pos hc0 _)) hpDom.1, hpDom.2.1⟩
  have hã_pos : 0 < fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α) := by
    rw [hatil_eq]; exact mul_pos (sq_pos_of_pos hτ₁_pos) hA_mem.1
  have hã_sz := fctAtil_size hc100 (û := -fctKappa c * fctAtil (concretePhiTilde K4 ε c) (concreteTau0 ε c S) (L1, α))
    rfl hadm_u FormalResearch.Special.airyZero_one hã_pos
  have hSA_hi : S.A q ≤ 4 * c ^ (-(1 / 6 : ℝ)) := by
    have hc_eq : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 6 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [hatil_eq, hτ₁_sq, hc_eq] at hã_sz
    exact le_of_mul_le_mul_left (a := c ^ (-(1 / 2 : ℝ))) (by linarith only [hã_sz.2]) (Real.rpow_pos_of_pos hc0 _)
  have h15 : 15 * S.ε ≤ 1 / 2 := by
    have hc_C0 : (30 * pbC0 + 1) ^ 2 ≤ c := (le_max_right _ _).trans hc
    have h1 : 30 * pbC0 + 1 ≤ c ^ (1 / 2 : ℝ) := by rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le hc_C0
    have hpos : (0 : ℝ) < 30 * pbC0 + 1 := by linarith only [pbC0_nonneg]
    have h2 : pbC0 * τ₁ ^ 2 ≤ 1 / 30 := by
      rw [hτ₁_sq, Real.rpow_neg hc0.le]
      calc pbC0 * (c ^ (1 / 2 : ℝ))⁻¹ ≤ pbC0 * (30 * pbC0 + 1)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ hpos h1) pbC0_nonneg
        _ ≤ 1 / 30 := by rw [← div_eq_mul_inv, div_le_div_iff₀ hpos (by norm_num)]; linarith only [pbC0_nonneg]
    rw [hSε]; linarith only [h2]
  have hell1_bd : |concreteEll1 ε c L1| ≤ 8 * c ^ (-(1 / 6 : ℝ)) := by
    have hr0 : S.r (q, 0) = 0 := by rw [hSr]; simp [CfuTheta.r]
    have h := abs_ell1_le_of_A hqΩ hr0 h15 hA_mem.1.le hSA_hi
    calc |concreteEll1 ε c L1| = |S.ℓ q| := by rw [hSℓ]
      _ ≤ 2 * (4 * c ^ (-(1 / 6 : ℝ))) := h
      _ = 8 * c ^ (-(1 / 6 : ℝ)) := by ring
  have hL1_bd : |L1| ≤ (8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ)) := by
    have hc1 : 1 ≤ c := by linarith only [hc100]
    have hL1_eq : L1 = concreteEll1 ε c L1 * τ₁ ^ 2 + ctTheta1 ε / c := by
      unfold concreteEll1
      have hne : (c ^ (-(1 / 4 : ℝ))) ^ 2 ≠ 0 := (sq_pos_of_pos hτ₁_pos).ne'
      field_simp [hne]; ring
    have hcinv : c⁻¹ ≤ c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hcexp : c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; congr 1; norm_num
    rw [hL1_eq]
    calc |concreteEll1 ε c L1 * τ₁ ^ 2 + ctTheta1 ε / c|
        ≤ |concreteEll1 ε c L1 * τ₁ ^ 2| + |ctTheta1 ε / c| := abs_add_le _ _
      _ = |concreteEll1 ε c L1| * c ^ (-(1 / 2 : ℝ)) + |ctTheta1 ε| * c⁻¹ := by
          rw [abs_mul, abs_of_pos (sq_pos_of_pos hτ₁_pos), hτ₁_sq, abs_div, abs_of_pos hc0]
          rw [div_eq_mul_inv (|ctTheta1 ε|) c]
      _ ≤ (8 * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) + |ctTheta1 ε| * c ^ (-(2 / 3 : ℝ)) := by
          gcongr
      _ = (8 + |ctTheta1 ε|) * c ^ (-(2 / 3 : ℝ)) := by rw [mul_assoc, hcexp]; ring
  have hO : IsOpen (S.Ω ×ˢ Yint) := S.hΩ.prod isOpen_Ioo
  have hV_sub_jc : JC 16 (S.Ω ×ˢ Yint) (fun y => S.V y - τs) (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ))) := by
    refine (S.out.2.2.2.2.2.2.2.2.2.1.congr ?_).mono (le_of_eq ?_)
    · intro y _; simp only [ChartSetup.V, ChartSetup.D, tauStar_eq_dStar_inv]
    · rw [hScV, hSε, hτ₁_sq]; ring
  have hUd_Yint : UniqueDiffOn ℝ Yint := isOpen_Ioo.uniqueDiffOn
  have hV_slice_jc : JC 16 Yint (fun y => S.V (q, y) - τs) ((Nat.factorial 16 : ℝ) * (pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)))) := by
    have hK_nn : 0 ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg (mul_nonneg pbcV_nonneg pbC0_nonneg) (by positivity)
    have hcomp := JC.comp_pair (k := 16) hUd_Yint hO.uniqueDiffOn
      (b1 := 1) (b2 := 1) hK_nn hV_sub_jc contDiffOn_const contDiffOn_id
      (fun j hj1 _ t ht => by
        change ‖iteratedFDerivWithin ℝ j (fun _ : ℝ => q) Yint t‖ ≤ 1
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hUd_Yint contDiffAt_const ht,
          iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
        simp)
      (fun j hj1 _ t ht => by
        change ‖iteratedFDerivWithin ℝ j (id : ℝ → ℝ) Yint t‖ ≤ 1
        exact norm_iteratedFDerivWithin_id_le hUd_Yint hj1 ht)
      (fun t ht => ⟨hqΩ, ht⟩)
    refine hcomp.mono (le_of_eq ?_)
    have hmax1 : max (1 : ℝ) (max 1 1) = 1 := by norm_num
    rw [hmax1, one_pow, mul_one]
  have hV_jets_ex : FctVJets pbKV c (concreteInnerV K4 ε c L1 α) ∧
      ∀ y ∈ Icc (0 : ℝ) 3.5, concreteInnerV K4 ε c L1 α y = S.V (q, y) := by
    have hV_slice_jc' : JC 16 Yint (fun y => S.V (q, y) - τs)
        (((Nat.factorial 16 : ℝ) * (pbcV * pbC0)) * c ^ (-(1 / 2 : ℝ))) :=
      hV_slice_jc.mono (le_of_eq (by ring))
    have hnn : 0 ≤ (Nat.factorial 16 : ℝ) * (pbcV * pbC0) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg pbcV_nonneg pbC0_nonneg)
    exact fctVJets_of_chartV.choose_spec.2 (c := c) (K₀ := (Nat.factorial 16 : ℝ) * (pbcV * pbC0)) hc0 hnn hV_slice_jc'
  have hVA_sub : |S.V (q, S.A q) - τs| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
    have hAY : (q, S.A q) ∈ S.Ω ×ˢ Yint := ⟨hqΩ, ⟨by linarith only [hA_mem.1], by linarith only [hA_mem.2]⟩⟩
    simpa [Real.norm_eq_abs] using hV_sub_jc.2 0 (by norm_num) (q, S.A q) hAY
  have hV0_sub : |concreteInnerV K4 ε c L1 α 0 - τs| ≤ pbcV * pbC0 * c ^ (-(1 / 2 : ℝ)) := by
    have h0Y : (q, (0 : ℝ)) ∈ S.Ω ×ˢ Yint := ⟨hqΩ, ⟨by norm_num, by norm_num⟩⟩
    have h0eq : concreteInnerV K4 ε c L1 α 0 = S.V (q, 0) := by
      dsimp only [concreteInnerV, S]; rw [clampY_eq_self (by norm_num : (0 : ℝ) ≤ 3.5)]
    rw [h0eq]
    simpa [Real.norm_eq_abs] using hV_sub_jc.2 0 (by norm_num) (q, (0 : ℝ)) h0Y
  exact ⟨hc0, hc100, hτ₁_sq, hqΩ, hell1, hA_mem, hSA_hi, hL1_bd, hV_slice_jc, hV_jets_ex, hVA_sub, hV0_sub⟩


end FormalResearch.SignUncertainty
