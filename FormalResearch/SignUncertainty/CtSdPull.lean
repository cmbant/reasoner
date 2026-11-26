module

public import FormalResearch.SignUncertainty.CtSdReal

/-!
# The pull-back data at a real parameter (`ct:cfu` Step 3, concrete data)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2/3.  **Proved.**
At a real `β` near `0`, the real chart `T(s;β)` satisfies the hypotheses `PullBack` of the abstract assembly
(`outer_assembly`): `B(T s) T'(s) = N_c s^{1/2} g_s(s)` for `B = √(πc/12) A_ε` and `ϕ(T s) = a s + s³/3`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

set_option linter.unusedSectionVars false

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtChart

lemma ysF_eq_neg_aC (β : ℂ) : ysF β = -aC β := by
  unfold ysF aC; ring

lemma Tf_zero_left (β : ℂ) : Tf (0, β) = 0 := by simp [Tf]

/-- The amplitude `E(z) = e^{-B_c(i T(z;β))}`. -/
noncomputable def Efun (c : ℝ) (β : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-(FormalResearch.Asymptotics.binetDiff c (Complex.I * Tf (z, β))))

/-- The prefactor `N_c = c^{1/2} π^{-1/2} e^{iπ/4}`. -/
noncomputable def Ncc (c : ℝ) : ℂ := ((Real.sqrt c / Real.sqrt π : ℝ) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ))

/-- The real amplitude `B = √(πc/12) A_ε`. -/
noncomputable def Bfun (ε c : ℝ) (τ : ℝ) : ℂ := ((Real.sqrt (π * c / 12) : ℝ) : ℂ) * CtOsc.outerAmp ε c τ

theorem pullBack_real {ε c β s1' psi : ℝ} {ϑ : ℂ → ℂ} {ρ : ℝ} (hreg : ChartReg ε ϑ ρ) (hc : 0 < c)
    (hs1' : s1' < ρ) (hβ : |β| < ρ) (hTb : ∀ s ∈ Icc (0 : ℝ) s1', |Treal β s| < 1 / 4)
    (haC : aC (β : ℂ) = ((CtCfu.AF β : ℝ) : ℂ)) (hpsi : psiHat ϑ (β : ℂ) = (psi : ℂ)) :
    PullBack s1' (CtCfu.AF β) (Ncc c) (gAmp (CtCfu.AF β) psi (fun z => Qeps ϑ (z, (β : ℂ))) (Efun c (β : ℂ)))
      (Treal β) (T1real β) (Bfun ε c) (phaseL (CtCfu.NF β)) := by
  have hβC : ‖(β : ℂ)‖ < ρ := by simpa using hβ
  have hsC : ∀ s : ℝ, |s| < ρ → ‖(s : ℂ)‖ < ρ := fun s hs => by simpa using hs
  have hsm : ∀ s ∈ Icc (0 : ℝ) s1', |s| < ρ := fun s hs => by
    rw [abs_of_nonneg hs.1]; linarith [hs.2]
  have hd : ∀ s ∈ Icc (0 : ℝ) s1', HasDerivAt (Treal β) (T1real β s) s ∧
      Tsd (((s : ℝ) : ℂ) ^ 2, (β : ℂ)) = ((T1real β s : ℝ) : ℂ) := fun s hs =>
    Treal_deriv (ρ := ρ) (fun z hz => (hreg z β hz hβC).2.1) (fun z hz => (hreg z β hz hβC).2.2.1) (hsm s hs)
  have hT1 : ∀ s ∈ Icc (0 : ℝ) s1', 0 < T1real β s := by
    intro s hs
    have := (hreg (s : ℂ) β (hsC s (hsm s hs)) hβC).2.2.2.2.2.2.2.2.1
    have h0 : 0 < 1 / (2 * CtCfu.d0) := by have := CtCfu.d0_pos; positivity
    exact lt_of_lt_of_le h0 (by simpa [T1real] using this)
  have hT0 : Treal β 0 = 0 := by simp [Treal, Tf_zero_left]
  have hpos := T_pos_of_deriv (fun s hs => (hd s hs).1) hT1 hT0
  refine ⟨fun s hs => (hd s hs).1, hT1, hT0, ?_, ?_⟩
  · intro s hs
    have hsI : s ∈ Icc (0 : ℝ) s1' := ⟨hs.1.le, hs.2⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hreg (s : ℂ) β (hsC s (hsm s hsI)) hβC
    have hTr := Tf_real_eq h3
    have hTp := hpos s hs
    have hT4 := hTb s hsI
    have hTl : Treal β s < 1 / 4 := (abs_lt.1 hT4).2
    have hT2 : Treal β s ^ 2 < CtCfu.rr := by
      have : (1 : ℝ) / 16 < CtCfu.rr := by
        unfold CtCfu.rr
        have := Real.pi_lt_four
        have := Real.pi_pos
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      nlinarith
    have hcpos := hc
    have hamp := amp_pull (ε := ε) (c := c) (β := β) (s := s) (psi := psi) (a := CtCfu.AF β) (ϑ := ϑ)
      (T := Treal β s) (T1 := T1real β s) hc hs.1 hTr hTp hT2 (by linarith) (hd s hsI).2 h6 h4 h5
      (by rw [ysF_eq_neg_aC, haC]) hpsi
    unfold Bfun Ncc Efun
    exact hamp
  · intro s hs
    have hsI : s ∈ Icc (0 : ℝ) s1' := hs
    obtain ⟨h1, h2, h3, -⟩ := hreg (s : ℂ) β (hsC s (hsm s hsI)) hβC
    have hT0' : 0 ≤ Treal β s := by
      rcases hs.1.eq_or_lt with h | h
      · rw [← h, hT0]
      · exact (hpos s ⟨h, hs.2⟩).le
    have hTl : Treal β s < 1 / 4 := (abs_lt.1 (hTb s hsI)).2
    have hT2 : Treal β s ^ 2 < CtCfu.rr := by
      have : (1 : ℝ) / 16 < CtCfu.rr := by
        unfold CtCfu.rr
        have := Real.pi_lt_four
        have := Real.pi_pos
        rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      nlinarith
    exact phase_pull h1 h3 haC hT0' hT2

lemma sg_le_one (τ : ℝ) : CtOsc.sg τ ≤ 1 := by
  unfold CtOsc.sg
  rw [div_le_one (by positivity)]; linarith [sq_nonneg τ]

/-- `m` is monotone on `(0, ∞)`. -/
lemma m_mono {C0 : ℝ} {m m1 m2 m3 : ℝ → ℝ} (hM : CtOsc.MData C0 m m1 m2 m3) :
    MonotoneOn m (Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · exact fun x hx => (hM.d0 x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hM.d0 x (by rwa [interior_Ioi] at hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hM.d0 x hx).deriv]; exact (hM.m1_pos hx).le

theorem tailBd_real {ε : ℝ} (hε : ε = -1 ∨ ε = 1) :
    ∃ C0 CA : ℝ, 0 ≤ C0 ∧ 0 ≤ CA ∧ ∀ {c s1 s1' K1 L a : ℝ} {T T1 : ℝ → ℝ}, 2 ≤ c → 0 < s1 → s1 < s1' → 0 < K1 →
      (∀ s ∈ Icc (0 : ℝ) s1', HasDerivAt T (T1 s) s) → (∀ s ∈ Icc (0 : ℝ) s1', phaseL L (T s) = a * s + s ^ 3 / 3) →
      0 < T s1 → 0 < T1 s1 → T1 s1 ≤ K1 → |a| ≤ s1 ^ 2 / 16 →
      ∃ B1 B2 : ℝ → ℂ, TailBd C0 (Real.sqrt (π * c / 12) * CA) (min 1 ((15 / 16) * s1 ^ 2 / K1)) L (T s1)
        hankelEdgeM (iteratedDeriv 1 hankelEdgeM) (iteratedDeriv 2 hankelEdgeM) (iteratedDeriv 3 hankelEdgeM)
        (Bfun ε c) B1 B2 (phaseL L) := by
  obtain ⟨C0, hC0, hMd⟩ := CtOsc.mdata_hankel
  obtain ⟨CA, hCA, hAmp⟩ := CtOsc.outerAmp_ampBd hε
  refine ⟨C0, CA, hC0.le, hCA, fun {c s1 s1' K1 L a T T1} hc hs1 hs1s hK1 hT hϕT hτ1 hT1 hT1K ha => ?_⟩
  obtain ⟨A1, A2, hA⟩ := hAmp c hc
  have hc0 : 0 < c := by linarith
  set k : ℝ := Real.sqrt (π * c / 12) with hk
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hkn : ‖(k : ℂ)‖ = k := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0]
  -- the gap `m(τ1) - L`
  have hgap : (15 / 16) * s1 ^ 2 / K1 ≤ hankelEdgeM (T s1) - L := by
    have hs1I : s1 ∈ Icc (0 : ℝ) s1' := ⟨hs1.le, hs1s.le⟩
    have h1 : HasDerivAt (fun s => phaseL L (T s)) ((hankelEdgeM (T s1) - L) * T1 s1) s1 :=
      (phaseL_deriv L hτ1).scomp s1 (hT s1 hs1I) |>.congr_deriv (by simp [mul_comm])
    have h2 : HasDerivAt (fun s : ℝ => a * s + s ^ 3 / 3) (a + s1 ^ 2) s1 := by
      have := ((hasDerivAt_id s1).const_mul a).add (((hasDerivAt_pow 3 s1).div_const 3))
      exact this.congr_deriv (by norm_num)
    have h3 : (fun s => phaseL L (T s)) =ᶠ[𝓝 s1] fun s : ℝ => a * s + s ^ 3 / 3 := by
      have : Icc (0 : ℝ) s1' ∈ 𝓝 s1 := Icc_mem_nhds hs1 hs1s
      filter_upwards [this] with s hs using hϕT s hs
    have h4 := h1.unique (h2.congr_of_eventuallyEq h3)
    have h5 : hankelEdgeM (T s1) - L = (a + s1 ^ 2) / T1 s1 := by
      field_simp; linarith [h4]
    rw [h5, div_le_div_iff₀ hK1 hT1]
    have : (15 / 16) * s1 ^ 2 ≤ a + s1 ^ 2 := by linarith [(abs_le.1 ha).1]
    nlinarith [mul_le_mul this hT1K hT1.le (by nlinarith [(abs_le.1 ha).1, sq_nonneg s1]), sq_nonneg s1]
  have hγ : 0 < min 1 ((15 / 16) * s1 ^ 2 / K1) := lt_min one_pos (div_pos (mul_pos (by norm_num) (pow_pos hs1 2)) hK1)
  refine ⟨fun τ => (k : ℂ) * A1 τ, fun τ => (k : ℂ) * A2 τ, hMd, by have := hA.CA0; positivity, hγ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun τ hτ => phaseL_deriv L hτ
  · intro τ hτ
    exact ((hA.d1 τ hτ).const_mul (k : ℂ))
  · intro τ hτ
    exact ((hA.d2 τ hτ).const_mul (k : ℂ))
  · exact continuousOn_const.mul hA.c2
  · intro τ hτ
    unfold Bfun
    rw [norm_mul, hkn]
    exact (mul_le_mul_of_nonneg_left (hA.b0 τ hτ) hk0.le).trans_eq (by ring)
  · intro τ hτ
    rw [norm_mul, hkn]
    exact (mul_le_mul_of_nonneg_left (hA.b1 τ hτ) hk0.le).trans_eq (by ring)
  · intro τ hτ
    rw [norm_mul, hkn]
    exact (mul_le_mul_of_nonneg_left (hA.b2 τ hτ) hk0.le).trans_eq (by ring)
  · intro τ hτ
    have hmono := m_mono hMd (show T s1 ∈ Ioi 0 from hτ1) (show τ ∈ Ioi 0 from lt_of_lt_of_le hτ1 hτ) hτ
    have h1 : min 1 ((15 / 16) * s1 ^ 2 / K1) ≤ hankelEdgeM τ - L := by
      refine (min_le_right _ _).trans (hgap.trans ?_)
      linarith
    have h2 : CtOsc.sg τ ≤ 1 := sg_le_one τ
    have h3 : min 1 ((15 / 16) * s1 ^ 2 / K1) * CtOsc.sg τ ≤ min 1 ((15 / 16) * s1 ^ 2 / K1) := by
      calc _ ≤ min 1 ((15 / 16) * s1 ^ 2 / K1) * 1 := mul_le_mul_of_nonneg_left h2 hγ.le
        _ = _ := mul_one _
    exact h3.trans (h1.trans (le_abs_self _))

end FormalResearch.SignUncertainty.CtSd
