module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasConcrete
public import FormalResearch.SignUncertainty.CtBoasTotal

/-!
# `ct:boas-ineq`: the concrete instance of `BoasInputs` (the core)

`constant_terms_lower.tex`, `ct:boas`: for one `c` in the regime, one `ε = ±1`, a good taper radius `R` and a feasible `f` with
`M[f] = 1`, all fields of `BoasInputs` for `h = hankelHL c f`, `X = boasX c ε`, `ν = boasNu c`, `wt = ctTaper ε c R`,
`sf = 𝔰_far ∘ Δ`, the tent partition on `a = (5/6) L_min`, are assembled and `boas_ineq_tent` gives
`ℬ ≥ -boasErrTotal` (`boas_concrete_core`).  The regime hypotheses are explicit numerical facts about `c` alone; they hold for
`c ≥ c₀` (`CtBoasRegime`).  **Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

lemma boasW_pos {c a : ℝ} (hc : 1 < c) (ha : 0 < a) (j : ℕ) : 0 < boasW c a j := by
  unfold boasW
  have h1 := tau0_pos (tentNode_pos ha (j + 1))
  have h2 : 0 < Real.log c := Real.log_pos hc
  have h3 := tentNode_pos ha (j + 1)
  positivity

lemma boasAj_nonneg {ε c R Cθ a : ℝ} (hc : 1 < c) (ha : 0 < a) (hCθ : 0 ≤ Cθ) (I : TaperChartInputs ε c R 2) (j : ℕ) :
    0 ≤ boasAj ε c R Cθ a j := by
  have hreg := I.reg
  have hCl0 : 0 ≤ boasCl Cθ a j := by
    have := boasLam_pos ha j
    unfold boasCl; exact mul_nonneg this.le (by positivity)
  unfold boasAj
  have h1 : 0 ≤ tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 2) a j :=
    tapMp_nonneg hreg ha (fun j => sigLip_nonneg (by linarith) _) j
  have h2 : 0 ≤ tapS (ctTaper ε c R) (taperKw 2) a j := tapS_nonneg hreg j
  positivity

lemma boasBj_nonneg {ε c R a : ℝ} (hc : 1 < c) (ha : 0 < a) (I : TaperChartInputs ε c R 2) (j : ℕ) :
    0 ≤ boasBj ε c R a j := by
  have hreg := I.reg
  have hCq0 : 0 ≤ boasCq c a j := mul_nonneg (by linarith) (boasLam_pos ha j).le
  unfold boasBj
  have h2 : 0 ≤ tapS (ctTaper ε c R) (taperKw 2) a j := tapS_nonneg hreg j
  positivity

lemma tentNode_pred_succ {a : ℝ} (ha : 0 < a) {J : ℕ} (hJ : 1 ≤ J) {b : ℝ} (hb : tentNode a (J - 1) < b) :
    tentNode a (J + 1) ≤ b + 1 / 18 := by
  obtain ⟨k, rfl⟩ : ∃ k, J = k + 1 := ⟨J - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hb
  have h1 : tentNode a (k + 1) ≤ tentNode a k + 1 / 36 := by
    rw [tentNode_succ]
    have := min_le_right (tentNode a k) 1
    linarith
  have h2 : tentNode a (k + 2) ≤ tentNode a (k + 1) + 1 / 36 := by
    rw [tentNode_succ a (k + 1)]
    have := min_le_right (tentNode a (k + 1)) 1
    linarith
  linarith

/-- **The grid**: the minimal node `J` with `x_J ≥ L_far + 1`, `L_far = log(π² log c)`, satisfies `x_{J+1} ≤ log c`,
`x_{j+1} ≤ L_far + 2` for `j < J`, and `J ≤ 400 log c`. -/
lemma boas_grid {c κ₀ a : ℝ} (hc0 : 0 < c) (hc1 : 1 < c) (hlog7 : 7 ≤ Real.log c) (hκ₀ : 0 < κ₀)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (haL : κ₀ * c ^ (-(2 / 21) : ℝ) ≤ a)
    (hlogc : Real.log (π ^ 2 * Real.log c) + 1 + 1 / 18 ≤ Real.log c)
    (hJb : 37 * |Real.log κ₀| + 3 ≤ 20 * Real.log c) :
    ∃ J : ℕ, 1 ≤ J ∧ Real.log (π ^ 2 * Real.log c) + 1 ≤ tentNode a J ∧ tentNode a (J + 1) ≤ Real.log c ∧
      (∀ j < J, tentNode a (j + 1) ≤ Real.log (π ^ 2 * Real.log c) + 2) ∧ (J : ℝ) ≤ 400 * Real.log c ∧
      3 ≤ Real.log (π ^ 2 * Real.log c) := by
  set Lfar : ℝ := Real.log (π ^ 2 * Real.log c) with hLfar_def
  have hπ2 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hLfar_exp : Real.exp Lfar = π ^ 2 * Real.log c := Real.exp_log (by positivity)
  have hLf3 : 3 ≤ Lfar := by
    have h1 : Real.exp 3 ≤ π ^ 2 * Real.log c := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have h3 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      have h4 : Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h3 3
      have h5 : 9 * 7 ≤ π ^ 2 * Real.log c := mul_le_mul hπ2.le hlog7 (by norm_num) (by positivity)
      linarith
    have := Real.log_le_log (Real.exp_pos 3) h1
    rwa [Real.log_exp] at this
  have hab : a < Lfar + 1 := by linarith
  obtain ⟨J, hJ1, hJb1, hJb2, hJcard⟩ := exists_tentNode_min ha0 ha1 hab
  have hx := tentNode_strictMono ha0
  have hxJ1 : tentNode a (J + 1) ≤ Real.log c := by
    have := tentNode_pred_succ ha0 hJ1 hJb2
    linarith
  have hxj : ∀ j < J, tentNode a (j + 1) ≤ Lfar + 2 := by
    intro j hj
    have h1 : tentNode a (j + 1) ≤ tentNode a (J - 1 + 1) := hx.monotone (by omega)
    have h2 : tentNode a (J - 1 + 1) ≤ tentNode a (J - 1) + 1 / 36 := by
      rw [tentNode_succ]; have := min_le_right (tentNode a (J - 1)) 1; linarith
    linarith
  -- `J ≤ 400 log c`
  have hJle : (J : ℝ) ≤ 400 * Real.log c := by
    have h1 : Real.log (1 / a) ≤ Real.log (1 / κ₀) + 2 / 21 * Real.log c := by
      have hpos : 0 < κ₀ * c ^ (-(2 / 21) : ℝ) := by positivity
      have h2 : Real.log (1 / a) ≤ Real.log (1 / (κ₀ * c ^ (-(2 / 21) : ℝ))) :=
        Real.log_le_log (by positivity) (one_div_le_one_div_of_le hpos haL)
      refine h2.trans (le_of_eq ?_)
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hκ₀.ne' (by positivity), Real.log_rpow hc0]
      ring
    have h3 : Real.log (1 / κ₀) ≤ |Real.log κ₀| := by
      rw [one_div, Real.log_inv]; exact neg_le_abs _
    have h4 : Lfar + 1 ≤ π ^ 2 * Real.log c := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < π ^ 2 * Real.log c); linarith
    have hπ2' : π ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h5 : π ^ 2 * Real.log c ≤ 10 * Real.log c :=
      mul_le_mul_of_nonneg_right hπ2' (Real.log_nonneg hc1.le)
    linarith
  exact ⟨J, hJ1, hJb1, hxJ1, hxj, hJle, hLf3⟩

set_option maxHeartbeats 4000000 in
/-- **The core: `BoasInputs` for the concrete data, and the bound `ℬ ≥ -boasErrTotal`** (one `c`, `ε`, `R`, `f`).  The hypotheses are the
top-scale moments of `f` (`ct_boas_moments_top`), the facts on `L_min = ctLv0 c` (`ctLv0_facts`), the taper band, and numerical
regime facts about `c` alone. -/
theorem boas_concrete_core {c c₁ K κ₀ Cθ ε T R LJ Lt : ℝ} {f : ℝ → ℝ}
    (hCθ0 : 0 ≤ Cθ)
    (hCθ : ∀ τ : ℝ, 1 ≤ τ → |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤ Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ)))
    (hθ' : ∀ t : ℝ, |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2)
    (hc₁ : 0 < c₁) (hK0 : 0 ≤ K) (hκ₀ : 0 < κ₀)
    (hε : ε = 1 ∨ ε = -1) (hf : IsHankelFeasible c ε T f) (hmass : hankelMass c f = 1)
    (hB : TaperBand ε c R) (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ))
    -- top-scale moments
    (hLJe : Real.exp LJ - 1 ≤ 5e-4) (hLJv : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ ctVprime c LJ)
    (hLt0 : 0 ≤ Lt) (hLtLJ : Lt ≤ LJ) (hLte : Real.exp Lt - 1 ≤ 5e-4) (hLtv : ctVprime c Lt ≤ 3)
    (hLT : ∀ L, Lt ≤ L → T ≤ c * (Real.exp L / π ^ 2)) (hTπ : T * π ^ 2 ≤ c * (1 + 5e-4))
    (hMom : ∫ L in Ioc 0 LJ, ctVprime c L * |hankelHL c f L| ≤ K * c ^ (1 / 3 : ℝ))
    (hTail : ∫ L in Ioi LJ, |hankelHL c f L| ≤ K * c ^ (-(1 / 3) : ℝ))
    -- `L_min`
    (hL0 : 0 < ctLv0 c) (hLe : Real.exp (ctLv0 c) - 1 ≤ 5e-4) (hLv : ctVprime c (ctLv0 c) = c ^ (4 / 7 : ℝ))
    (hLκ : κ₀ * c ^ (-(2 / 21) : ℝ) ≤ 5 / 6 * ctLv0 c)
    -- regime
    (hcs : max (Real.exp 7) (max 1 (84000 ^ 2 / κ₀)) ≤ c)
    (hF1 : 156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3) (hF2 : 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ))
    (hexp : Real.exp (-c) ≤ (c ^ 12)⁻¹) (hc47 : 2 ≤ c ^ (4 / 7 : ℝ))
    (hcR : c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (hR1 : 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ))
    (hlo : c ^ (-(1 / 3) : ℝ) ≤ κ₀ * c ^ (-(2 / 21) : ℝ))
    (hLt : 6 / (0.998 * langerScale c) ≤ κ₀ * c ^ (-(2 / 21) : ℝ))
    (hreg : 36000000 * Real.log c ≤ (κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c)
    (hlogc : Real.log (π ^ 2 * Real.log c) + 1 + 1 / 18 ≤ Real.log c)
    (hJb : 37 * |Real.log κ₀| + 3 ≤ 20 * Real.log c)
    (hfar : boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ) ≤ 60 * c ^ (-(2 : ℝ)))
    (hfE : farE2 c ≤ 2 * c ^ (-(2 : ℝ))) :
    -boasErrTotal c₁ K Cθ κ₀ c ≤
      ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
  have hc7 : Real.exp 7 ≤ c := (le_max_left _ _).trans hcs
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hI := hB.inputs
  have hf' := hf.toIsHankelEigenfn
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf'
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hf', hmass]
  set Lmin := ctLv0 c with hLmin
  set a : ℝ := 5 / 6 * Lmin with ha_def
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haL : κ₀ * c ^ (-(2 / 21) : ℝ) ≤ a := hLκ
  have ha1 : a ≤ 1 := by
    have : Lmin ≤ 5e-4 := by linarith [Real.add_one_le_exp Lmin]
    rw [ha_def]; linarith
  set Lmin := ctLv0 c with hLmin
  set a : ℝ := 5 / 6 * Lmin with ha_def
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haL : κ₀ * c ^ (-(2 / 21) : ℝ) ≤ a := hLκ
  have ha1 : a ≤ 1 := by
    have : Lmin ≤ 5e-4 := by linarith [Real.add_one_le_exp Lmin]
    rw [ha_def]; linarith
  set Lfar : ℝ := Real.log (π ^ 2 * Real.log c) with hLfar_def
  obtain ⟨J, hJ1, hJb1, hxJ1, hxj, hJle, hLf3⟩ := boas_grid hc0 hc1 hlog7 hκ₀ ha0 ha1 haL hlogc hJb
  have hx := tentNode_strictMono ha0
  have hLJ0 : 0 ≤ LJ := hLt0.trans hLtLJ
  have hR1' : 1 ≤ R := hR1.trans hRlo
  have hRm : c ^ (4 / 7 : ℝ) + 1 / 2 ≤ R := hcR.trans hRlo
  obtain ⟨hΛJ, hgeom⟩ := boas_geometry hc0 hB hLJ0 hLJe hLJv hRhi
  have hLΛ : Lmin ≤ ctTaperLam ε c R := lmin_le_lam hc0 hB hL0.le hLe hLv hRm
  have hLJ : Lmin ≤ LJ := hLΛ.trans hΛJ
  have hLJ5 : LJ ≤ 5e-4 := by linarith [Real.add_one_le_exp LJ]
  have hΛlt : ctTaperLam ε c R < Lfar - 5 / 2 := by linarith
  -- setting
  have hS : BoasSetting (hankelHL c f) (boasX c ε) (boasNu c) (ctTaper ε c R) (boasSf c) :=
    ⟨hh, measurable_boasX c ε, measurable_boasNu c, measurable_ctTaper hI, measurable_sFar_comp hc1,
      fun L => hI.reg.mem L, fun L => ⟨sFar_nonneg hc1 _, sFar_le_one hc1 _⟩⟩
  have hw : ∀ L, 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1 := fun L => hI.reg.mem L
  have hsf : ∀ L, boasSf c L = sFar c (c * (Real.exp L / π ^ 2)) := fun L => rfl
  have hlog2 : 2 ≤ Real.log c := by linarith
  -- far
  have hπ2 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hT1 : T ≤ c := by
    by_contra h
    rw [not_le] at h
    have := mul_lt_mul_of_pos_left hπ2 (by linarith : 0 < T)
    linarith
  have hcl : c ≤ farD c / 2 := by
    unfold farD
    nlinarith
  have hLminfar : c * (Real.exp Lmin / π ^ 2) ≤ farD c / 2 := by
    have h1 : Real.exp Lmin ≤ π ^ 2 := by linarith [hLe]
    have h2 : Real.exp Lmin / π ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h1
    nlinarith
  have hn : 2 ≤ ⌈c ^ 2⌉₊ := by
    have : (2 : ℝ) ≤ c ^ 2 := by nlinarith
    have h2 : (2 : ℝ) ≤ (⌈c ^ 2⌉₊ : ℝ) := this.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have hfarI := boas_far_field_hankel (wt := ctTaper ε c R) (sf := boasSf c) (Lmin := Lmin) hc1 hlog2 hε.symm hCθ hf hmass
    (by linarith) hn (measurable_ctTaper hI) (measurable_sFar_comp hc1) hw hsf (ctTaper_hwt1 hc1 hI) hLminfar
    (measurable_boasX c ε)
  -- trunc_hi
  have hthi : ∫ L in Ioi (Lfar + 1), ctTaper ε c R L * (1 - boasSf c L) * |hankelHL c f L| ≤ 2 * c ^ (-(2 : ℝ)) := by
    have := boas_trunc_hi hc1 hh hw hsf (Lfar := Lfar) (by rw [Real.exp_log (by positivity)])
    rw [hmass1, mul_one] at this
    exact this.trans hfE
  -- trunc_lo
  have htlo := boas_field_trunc_lo hc3 hB hc₁ hRlo hh hmass1 hL0 hLe hLv hLΛ hLJ hLJe hK0 hMom
  -- e fields
  have hUf := boas_U_facts (J := J) (a := a) hc0 ha_def hL0 ha1 hLe hLv hB.Lam_le_small hc47
  obtain ⟨he0, heint, hemom⟩ := boas_field_e (J := J) (a := a) hc3 hB hc₁ hRlo hR1' hh hLJ0 hLJe hΛJ hgeom hUf hK0
    hMom hTail
  -- s field
  have hB2 : ∫ L in Ioi (ctTaperLam ε c R), |hankelHL c f L| ≤ (2 * K / c₁ ^ 2 + K) * c ^ (-(1 / 3) : ℝ) :=
    (tail_chebyshev (R' := R - 1 / 2) hh hc0 hLJe hI.Lam_pos.le hΛJ (by linarith)
      (fun L hL => hgeom L hL.1.le hL.2) hMom hTail).trans (B2_arith hc1.le hc₁ hK0 hR1' hRlo)
  have hsm := boas_field_s (J := J) (a := a) hκ₀ hcs haL ha1 hxj hh hmass1 hΛlt hB2
  -- P_lb
  have hLTa : Lt ≤ a / 2 := by
    have hK := langerScale_pos hc0
    have h1 : 0.998 * langerScale c * Lt ≤ 3 := (ctVprime_bounds hc0 hLt0 hLte).1.trans hLtv
    have h2 : Lt ≤ 3 / (0.998 * langerScale c) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h3 : 3 / (0.998 * langerScale c) = 6 / (0.998 * langerScale c) / 2 := by ring
    linarith
  have hPlb := boas_field_Plb (J := J) hc3 hF1 hF2 hf hε hmass ha0 ha1 (hlo.trans haL) hxJ1 hLT hLTa
    (hreg.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) haL 3) hc0.le))
    hexp (boasX c ε) (ctTaper ε c R) (boasSf c)
  have hI' : BoasInputs (hankelHL c f) (boasX c ε) (boasNu c) (ctTaper ε c R) (boasSf c) Lmin Lfar J
      (tent (tentNode a)) (tentQ a) (boasW c a) (boasAj ε c R Cθ a) (boasBj ε c R a) (boasKd a) (boasSj c a)
      (boasEU ε c R a J) 1 (60 * c ^ (-(2 : ℝ))) (2 * c ^ (-(2 : ℝ)))
      (2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ)) (30 * (c ^ 4)⁻¹)
      (15552000000 * Real.log c / (a ^ 3 * c ^ 2)) (boasKstarC Cθ) (boasCe c₁ K * (c ^ (-(4 / 3) : ℝ) * Real.log c))
      (7 * (Real.exp (-(Real.log c ^ 2)) + 2000 * Real.log c / c * ((2 * K / c₁ ^ 2 + K) * c ^ (-(1 / 3) : ℝ)))) :=
    { mass := hmass1.le
      far := by linarith
      trunc_hi := hthi
      trunc_lo := htlo
      Pb_nonneg := by positivity
      W_pos := fun j _ => boasW_pos hc1 ha0 j
      A_nonneg := fun j _ => boasAj_nonneg hc1 ha0 hCθ0 hI j
      Kd_nonneg := fun j _ => by unfold boasKd; positivity
      P_lb := hPlb
      freeze := boas_field_freeze (J := J) hc3 hCθ0 ha0 hθ' hI
      Kd_W := fun j _ => boas_Kd_W_field hc1.le ha0 ha1 j
      pointwise := fun j hj L hL => by
        have hLU : L ∈ ⋃ j ∈ Finset.range J, tentQ a j := Set.mem_biUnion (Finset.mem_range.2 hj) hL
        have := boas_field_pointwise (J := J) (a := a) hc3 hCθ0 ha0 hI j hj L hL
        unfold boasEU
        rw [Set.indicator_of_mem hLU]
        exact this
      Kstar_nonneg := boasKstarC_nonneg hCθ0
      e_nonneg := he0
      e_int := heint
      e_moment := hemom
      s_moment := hsm }
  have hmain := boas_ineq_tent hL0 hJb1 hS hI'
  rw [← ha_def] at hmain
  refine le_trans (neg_le_neg ?_) hmain
  unfold boasErrTotal
  have hPb : 30 * (c ^ 4)⁻¹ * (tentNode a (J + 1) - a) ≤ 30 * (c ^ 4)⁻¹ * Real.log c :=
    mul_le_mul_of_nonneg_left (by linarith [ha0]) (by positivity)
  have hκ : 15552000000 * Real.log c / (a ^ 3 * c ^ 2) ≤
      15552000000 * Real.log c / ((κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) haL 3) (by positivity))
  have hJκ : (J : ℝ) * (15552000000 * Real.log c / (a ^ 3 * c ^ 2)) * 1 ≤
      400 * Real.log c * (15552000000 * Real.log c / ((κ₀ * c ^ (-(2 / 21) : ℝ)) ^ 3 * c ^ 2)) := by
    rw [mul_one]; exact mul_le_mul hJle hκ (by positivity) (by positivity)
  linarith

end FormalResearch.SignUncertainty
