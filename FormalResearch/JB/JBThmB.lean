module

public import Mathlib
public import FormalResearch.JB.JBOneStep

/-!
# Paper J, Theorem B, conditional on the one-step inputs (`thm:B`, `thm:thb-onestep`, quantified form)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Theorem `thm:B` (`eq:thmB`) and its proof.

`thm_B_conditional` is the paper's quantifier order (F2): for a family of `OneStepInputs`, one for each
`N`, with `D = N + 1` columns and step `h = L/(N+1)`, for fixed constants `cs`:

* there are `C` and `h₀ > 0` with `‖Ĝ_m - U_h‖ ≤ C h^m` for all `N` with `h ≤ h₀`;
* there is `h_m ≤ h₀` with `C h_m^m < 1` such that for `h ≤ h_m` the polar factor of `Ĝ_m` is orthogonal and
  `‖polar - U_h‖ ≤ 2 C h^m`.

Where `D = L/h` enters: only in `Small` (`jb_onestep`), as `√D · C h^{m+1} log(1/h) ≤ 2 C √L h^m`
(`sqrt_mul_eta_le`, using `√(L/h) · h^{m+1/2} log(1/h) ≤ 2 h^m`, from `log(1/h) ≤ 2/√h`) and as
`2 D ε5 ≤ h^m` for `ε5 ≤ C_ε h^{-K_ε} e^{-c_ε/h}`, i.e. `x^{K_ε + 1 + m} e^{-c_ε x} → 0` for `x = 1/h`
(`eventually_small_tail`, Mathlib's `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`).

Hypotheses (not proved here): the family of `OneStepInputs` (this is `prop:thb-inputs`, i.e. Theorem A(ii)
and the charts), with the same constants `cs` for all `N` (uniformity), and the form of (I5):
`ε5 ≤ C_ε (1/h)^{K_ε} exp(-c_ε/h)`.  The conclusion is for the matrices `Ĝ_m = (Inp N).G0`.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

/-- The step `h = L/(N+1)`. -/
noncomputable def stepSize (L : ℝ) (N : ℕ) : ℝ := L / ((N : ℝ) + 1)

theorem stepSize_pos {L : ℝ} (hL : 0 < L) (N : ℕ) : 0 < stepSize L N := by
  unfold stepSize; positivity

/-- `D = N + 1 = L / h`. -/
theorem card_eq_div {L : ℝ} (hL : 0 < L) (N : ℕ) : (((N + 1 : ℕ)) : ℝ) = L / stepSize L N := by
  unfold stepSize
  push_cast
  field_simp

theorem sqrt_mul_eta_le {L h C : ℝ} (m : ℕ) (hL : 0 < L) (hh : 0 < h) (hC : 0 ≤ C) :
    √(L / h) * (C * h ^ (m + 1) * Real.log (1 / h)) ≤ 2 * C * √L * h ^ m := by
  have hs : 0 < √h := Real.sqrt_pos.2 hh
  have hs2 : √h * √h = h := Real.mul_self_sqrt hh.le
  have hlog : Real.log (1 / h) ≤ 2 / √h := by
    have e : Real.log (1 / h) = 2 * Real.log (1 / √h) := by
      have : 1 / h = (1 / √h) ^ 2 := by
        rw [div_pow, one_pow, sq, hs2]
      rw [this, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / √h by positivity)
    rw [e]
    have h3 : 2 * (1 / √h) = 2 / √h := by ring
    linarith
  rw [Real.sqrt_div hL.le]
  have hpos : 0 ≤ √L / √h * (C * h ^ (m + 1)) := by positivity
  have e2 : √L / √h * (C * h ^ (m + 1)) * (2 / √h) = 2 * C * √L * h ^ m := by
    have : √L / √h * (C * h ^ (m + 1)) * (2 / √h) = 2 * C * √L * h ^ (m + 1) / (√h * √h) := by
      field_simp
    rw [this, hs2, pow_succ]
    field_simp
  calc √L / √h * (C * h ^ (m + 1) * Real.log (1 / h))
      = (√L / √h * (C * h ^ (m + 1))) * Real.log (1 / h) := by ring
    _ ≤ (√L / √h * (C * h ^ (m + 1))) * (2 / √h) := mul_le_mul_of_nonneg_left hlog hpos
    _ = 2 * C * √L * h ^ m := e2

theorem eventually_small_tail (a : ℕ) (b A : ℝ) (hb : 0 < b) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 0 < x → A * (x ^ a * Real.exp (-b * x)) ≤ 1 := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a : ℝ) b hb
  have hev : ∀ᶠ x : ℝ in Filter.atTop, x ^ (a : ℝ) * Real.exp (-b * x) < 1 / (|A| + 1) :=
    (tendsto_order.1 ht).2 _ (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨x₀, fun x hx hx0 => ?_⟩
  have h1 := hx₀ x hx
  rw [Real.rpow_natCast] at h1
  have h2 : 0 ≤ x ^ a * Real.exp (-b * x) := by positivity
  calc A * (x ^ a * Real.exp (-b * x)) ≤ |A| * (x ^ a * Real.exp (-b * x)) := by
        gcongr; exact le_abs_self A
    _ ≤ |A| * (1 / (|A| + 1)) := by gcongr
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

/-- The explicit smallness conditions of `OneStepInputs.Small` hold for all `h ≤ h₁`, when
`D = L/h` and `ε5 ≤ C_ε (1/h)^{K_ε} exp(-c_ε/h)`. -/
theorem small_scalars (cs : OneStepConsts) {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L) (Cε cε : ℝ)
    (Kε : ℕ) (hcε : 0 < cε) :
    ∃ h₁ : ℝ, 0 < h₁ ∧ ∀ h : ℝ, 0 < h → h ≤ h₁ →
      h ≤ 1 ∧ √(L / h) * (cs.C * h ^ (m + 1) * Real.log (1 / h)) ≤ 1 ∧
        cs.K * cs.C4 * h ^ m ≤ 1 / 2 ∧ cs.C * h ^ m ≤ cs.c0 / 2 ∧ h * cs.K * cs.ωmax ≤ 1 / 2 ∧
        2 * (L / h) * (Cε * (1 / h) ^ Kε * Real.exp (-cε / h)) ≤ h ^ m := by
  have hKn := cs.K_nonneg
  have hC4 := cs.C4_nonneg
  have hCn := cs.C_nonneg
  have hω := cs.ωmax_pos
  have hc0 := cs.c0_pos
  obtain ⟨x₀, hx₀⟩ := eventually_small_tail (Kε + 1 + m) cε (2 * L * Cε) hcε
  set X : ℝ := max x₀ 1 with hX
  have hX1 : 1 ≤ X := le_max_right _ _
  have hX0 : 0 < X := by linarith
  refine ⟨min (1 / (2 * cs.C * √L + 1)) (min (1 / (2 * cs.K * cs.C4 + 1))
    (min (cs.c0 / (2 * cs.C + 1)) (min (1 / (2 * cs.K * cs.ωmax + 1)) (1 / X)))), ?_, ?_⟩
  · refine lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  intro h hh hh1
  have b1 : h ≤ 1 / (2 * cs.C * √L + 1) := hh1.trans (min_le_left _ _)
  have b2 : h ≤ 1 / (2 * cs.K * cs.C4 + 1) := hh1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have b3 : h ≤ cs.c0 / (2 * cs.C + 1) :=
    hh1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have b4 : h ≤ 1 / (2 * cs.K * cs.ωmax + 1) :=
    hh1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have b5 : h ≤ 1 / X :=
    hh1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_right _ _))))
  have hsL : 0 ≤ √L := Real.sqrt_nonneg _
  have c1 : h * (2 * cs.C * √L + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 b1
  have c2 : h * (2 * cs.K * cs.C4 + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 b2
  have c3 : h * (2 * cs.C + 1) ≤ cs.c0 := (le_div_iff₀ (by positivity)).1 b3
  have c4 : h * (2 * cs.K * cs.ωmax + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 b4
  have hh1' : h ≤ 1 := by
    have : 0 ≤ 2 * cs.C * √L := by positivity
    nlinarith
  have hhm : h ^ m ≤ h := pow_le_of_le_one hh.le hh1' (by omega)
  have hhm0 : 0 ≤ h ^ m := by positivity
  refine ⟨hh1', ?_, ?_, ?_, ?_, ?_⟩
  · refine (sqrt_mul_eta_le m hL hh hCn).trans ?_
    have : 0 ≤ 2 * cs.C * √L := by positivity
    nlinarith
  · have : 0 ≤ cs.K * cs.C4 := by positivity
    nlinarith
  · nlinarith
  · nlinarith
  · -- the tail `2 D ε5 ≤ h^m`
    set x : ℝ := 1 / h with hx
    have hx0 : 0 < x := by positivity
    have hxX : x₀ ≤ x := by
      have : X ≤ x := by
        rw [hx, le_div_iff₀ hh]
        have := (le_div_iff₀ hX0).1 b5
        linarith
      exact (le_max_left _ _).trans this
    have key := hx₀ x hxX hx0
    have hxh : h = x⁻¹ := by rw [hx]; field_simp
    have e1 : L / h = L * x := by rw [hxh, div_inv_eq_mul]
    have e2 : -cε / h = -cε * x := by rw [hxh, div_inv_eq_mul]
    rw [e1, e2]
    have hxm : 0 < x ^ m := by positivity
    have hhm' : h ^ m = 1 / x ^ m := by rw [hxh, inv_pow, one_div]
    have eq : 2 * (L * x) * (Cε * x ^ Kε * Real.exp (-cε * x)) =
        (2 * L * Cε * (x ^ (Kε + 1 + m) * Real.exp (-cε * x))) / x ^ m := by
      field_simp
      ring
    rw [eq, hhm']
    exact div_le_div_of_nonneg_right key hxm.le

/-- **Theorem B, conditional on the one-step inputs** (Paper J `thm:B`, `eq:thmB`; the paper's quantifier
order).  For a family `Inp N` of one-step inputs with `D = N + 1` columns, step `h = L/(N+1)` and fixed
constants `cs` (this family is `prop:thb-inputs`, an input), with (I5) in the form
`ε5 ≤ C_ε (1/h)^{K_ε} exp(-c_ε/h)`: there are `C` and `h₀ > 0` with `‖Ĝ_m - U_h‖ ≤ C h^m` for `h ≤ h₀`,
and `h_m ≤ h₀` with `C h_m^m < 1` such that for `h ≤ h_m` the polar factor
`Ĝ_m (Ĝ_mᵀ Ĝ_m)^{-1/2}` is orthogonal and within `2 C h^m` of `U_h`.  Not covered: the verification of the
inputs (Theorem A(ii), the charts). -/
theorem thm_B_conditional (cs : OneStepConsts) (m : ℕ) {L : ℝ} (hL : 0 < L) (Cε cε : ℝ) (Kε : ℕ)
    (hcε : 0 < cε) (Inp : ∀ N : ℕ, OneStepInputs cs (N + 1) m (stepSize L N))
    (hε5 : ∀ N : ℕ, (Inp N).ε5 ≤ Cε * (1 / stepSize L N) ^ Kε * Real.exp (-cε / stepSize L N)) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧
      (∀ N : ℕ, stepSize L N ≤ h₀ → ‖(Inp N).G0 - (Inp N).U‖ ≤ C * stepSize L N ^ m) ∧
      ∃ hp : ℝ, 0 < hp ∧ hp ≤ h₀ ∧ C * hp ^ m < 1 ∧
        ∀ N : ℕ, stepSize L N ≤ hp →
          ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹)ᵀ *
              ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹) = 1 ∧
            ‖(Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹ - (Inp N).U‖ ≤
              2 * C * stepSize L N ^ m := by
  have hm : 1 ≤ m := (Inp 0).one_le_m
  obtain ⟨Cstar, hC⟩ := jb_onestep cs m
  obtain ⟨h₁, hh₁, hsm⟩ := small_scalars cs hm hL Cε cε Kε hcε
  have hCn := cs.C_nonneg
  have hsL : 0 ≤ √L := Real.sqrt_nonneg _
  set C : ℝ := max Cstar 0 + 2 * cs.C * √L with hCdef
  have hC0 : 0 ≤ C := by
    have : 0 ≤ max Cstar 0 := le_max_right _ _
    have : 0 ≤ 2 * cs.C * √L := by positivity
    linarith
  -- the reduction applies for `h ≤ h₁`, with the explicit dependence on `D = L/h`
  have key : ∀ N : ℕ, stepSize L N ≤ h₁ →
      ‖(Inp N).G0 - (Inp N).U‖ ≤ C * stepSize L N ^ m ∧
        (‖(Inp N).G0 - (Inp N).U‖ < 1 →
          ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹)ᵀ *
              ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹) = 1 ∧
            ‖(Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹ - (Inp N).U‖ ≤
              2 * ‖(Inp N).G0 - (Inp N).U‖) := by
    intro N hN
    have hpos := stepSize_pos hL N
    obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsm _ hpos hN
    have hD := card_eq_div hL N
    have hsmall : (Inp N).Small := by
      refine ⟨s1, ?_, s3, s4, s5, ?_⟩
      · rw [hD]; exact s2
      · rw [hD]
        calc 2 * (L / stepSize L N) * (Inp N).ε5
            ≤ 2 * (L / stepSize L N) *
              (Cε * (1 / stepSize L N) ^ Kε * Real.exp (-cε / stepSize L N)) := by
              gcongr; exact hε5 N
          _ ≤ _ := s6
    obtain ⟨-, r2, r3⟩ := hC (N + 1) (stepSize L N) (Inp N) hsmall
    refine ⟨?_, r3⟩
    have e1 : √(((N + 1 : ℕ) : ℝ)) * (cs.C * stepSize L N ^ (m + 1) * Real.log (1 / stepSize L N)) ≤
        2 * cs.C * √L * stepSize L N ^ m := by
      rw [hD]; exact sqrt_mul_eta_le m hL hpos hCn
    have hhm : 0 ≤ stepSize L N ^ m := by positivity
    calc ‖(Inp N).G0 - (Inp N).U‖ ≤ Cstar * stepSize L N ^ m +
          √(((N + 1 : ℕ) : ℝ)) * (cs.C * stepSize L N ^ (m + 1) * Real.log (1 / stepSize L N)) := r2
      _ ≤ max Cstar 0 * stepSize L N ^ m + 2 * cs.C * √L * stepSize L N ^ m := by
          gcongr
          exact le_max_left _ _
      _ = C * stepSize L N ^ m := by rw [hCdef]; ring
  refine ⟨C, h₁, hh₁, fun N hN => (key N hN).1, min h₁ (1 / (C + 1)), lt_min hh₁ (by positivity),
    min_le_left _ _, ?_, ?_⟩
  · have hp1 : min h₁ (1 / (C + 1)) ≤ 1 / (C + 1) := min_le_right _ _
    have hp0 : 0 < min h₁ (1 / (C + 1)) := lt_min hh₁ (by positivity)
    have hc1 : min h₁ (1 / (C + 1)) * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 hp1
    have hp1' : min h₁ (1 / (C + 1)) ≤ 1 := by nlinarith
    have : min h₁ (1 / (C + 1)) ^ m ≤ min h₁ (1 / (C + 1)) := pow_le_of_le_one hp0.le hp1' (by omega)
    nlinarith
  · intro N hN
    have hN1 : stepSize L N ≤ h₁ := hN.trans (min_le_left _ _)
    have hpos := stepSize_pos hL N
    have hp0 : 0 < min h₁ (1 / (C + 1)) := lt_min hh₁ (by positivity)
    have hp1 : min h₁ (1 / (C + 1)) ≤ 1 / (C + 1) := min_le_right _ _
    have hc1 : min h₁ (1 / (C + 1)) * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 hp1
    have hp1' : min h₁ (1 / (C + 1)) ≤ 1 := by nlinarith
    have hpm : min h₁ (1 / (C + 1)) ^ m ≤ min h₁ (1 / (C + 1)) :=
      pow_le_of_le_one hp0.le hp1' (by omega)
    have hhm : stepSize L N ^ m ≤ min h₁ (1 / (C + 1)) ^ m := pow_le_pow_left₀ hpos.le hN m
    have hlt : C * stepSize L N ^ m < 1 := by nlinarith
    obtain ⟨r1, r2⟩ := key N hN1
    obtain ⟨o1, o2⟩ := r2 (r1.trans_lt hlt)
    exact ⟨o1, by nlinarith⟩

/-- info: 'FormalResearch.JB.thm_B_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.thm_B_conditional

/-- The same statement as `thm_B_conditional`, in the form "`∃ C N₀, ∀ N ≥ N₀`" (`h = L/(N+1) ≤ h_m`). -/
theorem thm_B_conditional_atTop (cs : OneStepConsts) (m : ℕ) {L : ℝ} (hL : 0 < L) (Cε cε : ℝ)
    (Kε : ℕ) (hcε : 0 < cε) (Inp : ∀ N : ℕ, OneStepInputs cs (N + 1) m (stepSize L N))
    (hε5 : ∀ N : ℕ, (Inp N).ε5 ≤ Cε * (1 / stepSize L N) ^ Kε * Real.exp (-cε / stepSize L N)) :
    ∃ (C : ℝ) (N₀ : ℕ), ∀ N : ℕ, N₀ ≤ N →
      ‖(Inp N).G0 - (Inp N).U‖ ≤ C * stepSize L N ^ m ∧ C * stepSize L N ^ m < 1 ∧
        ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹)ᵀ *
            ((Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹) = 1 ∧
          ‖(Inp N).G0 * (CFC.sqrt ((Inp N).G0ᵀ * (Inp N).G0))⁻¹ - (Inp N).U‖ ≤
            2 * C * stepSize L N ^ m := by
  obtain ⟨C, h₀, hh₀, hb, hp, hp0, hph, hlt, hpol⟩ :=
    thm_B_conditional cs m hL Cε cε Kε hcε Inp hε5
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (L / hp)
  refine ⟨C, N₀, fun N hN => ?_⟩
  have hle : stepSize L N ≤ hp := by
    unfold stepSize
    rw [div_le_iff₀ (by positivity)]
    have h1 : L / hp ≤ (N : ℝ) + 1 := by
      have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [div_le_iff₀ hp0] at h1
    linarith
  have hlt' : C * stepSize L N ^ m < 1 := by
    have hpos := stepSize_pos hL N
    have h2 : stepSize L N ^ m ≤ hp ^ m := pow_le_pow_left₀ hpos.le hle m
    have hs0 : 0 ≤ stepSize L N ^ m := by positivity
    rcases le_or_gt 0 C with hC0 | hC0
    · calc C * stepSize L N ^ m ≤ C * hp ^ m := mul_le_mul_of_nonneg_left h2 hC0
        _ < 1 := hlt
    · nlinarith
  obtain ⟨o1, o2⟩ := hpol N hle
  exact ⟨hb N (hle.trans hph), hlt', o1, o2⟩

/-- info: 'FormalResearch.JB.thm_B_conditional_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.thm_B_conditional_atTop

end FormalResearch.JB
