module

public import FormalResearch.SignUncertainty.ShellGapExtract
public import FormalResearch.SignUncertainty.ShellGapProfileConv
public import FormalResearch.Analysis.QualCompact

/-!
# Auxiliary estimates for the endpoint clause of `thm:ce-shell-gap`

* `hankelMass_plus_le`, `hankelMass_minus_le`: for a Hankel Cohn-Elkies profile `G` (`d ≥ 2`),
  `M[p], M[q] ≤ M[G]` for `p = (h + ĥ)/2`, `q = (ĥ - h)/2`; this is what allows the normalisation `M[h] = 1` of
  `thm:ce-physical-profile` in place of `M[q] = 1` used by `extract_two`.
* `tail_small`: the uniform tail bound `eq:qual-compact-tight` for the window profiles of an eigenfunction
  sequence, from the deep-lobe mass estimate.
* `setIntegral_Icc_abs_sub_tendsto`: local uniform convergence gives local `L¹` convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

namespace HankelShellProfile

variable {c T : ℝ} {G : ℝ → ℝ}

/-- `h(0) ≤ M[h]`. -/
lemma origin_le_hankelMass {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    G 0 ≤ hankelMass ((d : ℝ) / 2) G := by
  have hc0 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  rw [← P.integral_eq hd]
  unfold hankelMass
  refine setIntegral_mono_on P.int (abs_mul_rho0_integrableOn hc0 P.int) measurableSet_Ioi
    fun s hs => ?_
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (hankelRho0_nonneg hc0 (le_of_lt hs))

lemma hankelMass_plus_le {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    hankelMass ((d : ℝ) / 2) (hankelPlus ((d : ℝ) / 2) G) ≤ hankelMass ((d : ℝ) / 2) G := by
  have hc0 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have h1 := hankelMass_smul ((d : ℝ) / 2) (1 / 2 : ℝ)
    (fun Δ => G Δ + besselHankelTransform ((d : ℝ) / 2) G Δ)
  have h2 := hankelMass_add_le hc0 P.int P.int_hat
  have h3 := P.hankelMass_hat hd
  have h4 := P.origin_le_hankelMass hd
  have e : hankelPlus ((d : ℝ) / 2) G =
      fun Δ => (1 / 2 : ℝ) * (G Δ + besselHankelTransform ((d : ℝ) / 2) G Δ) := rfl
  rw [e, h1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

lemma hankelMass_minus_le {d : ℕ} (hd : 2 ≤ d) (P : HankelShellProfile ((d : ℝ) / 2) T G) :
    hankelMass ((d : ℝ) / 2) (hankelMinus ((d : ℝ) / 2) G) ≤ hankelMass ((d : ℝ) / 2) G := by
  have hc0 : 0 < (d : ℝ) / 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have h1 := hankelMass_smul ((d : ℝ) / 2) (1 / 2 : ℝ)
    (fun Δ => besselHankelTransform ((d : ℝ) / 2) G Δ + (-1 : ℝ) * G Δ)
  have hneg : IntegrableOn (fun Δ => ((-1 : ℝ) * G Δ) * hankelRho0 ((d : ℝ) / 2) Δ) (Ioi 0) :=
    (P.int.neg).congr_fun (fun Δ _ => by simp) measurableSet_Ioi
  have h2 := hankelMass_add_le hc0 P.int_hat hneg
  have h3 := P.hankelMass_hat hd
  have h4 := P.origin_le_hankelMass hd
  have h5 := hankelMass_smul ((d : ℝ) / 2) (-1 : ℝ) G
  rw [abs_neg, abs_one, one_mul] at h5
  have e : hankelMinus ((d : ℝ) / 2) G =
      fun Δ => (1 / 2 : ℝ) * (besselHankelTransform ((d : ℝ) / 2) G Δ + (-1 : ℝ) * G Δ) := by
    funext Δ; unfold hankelMinus; ring
  rw [e, h1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h2' : hankelMass ((d : ℝ) / 2) (fun Δ => besselHankelTransform ((d : ℝ) / 2) G Δ + (-1 : ℝ) * G Δ) ≤
      hankelMass ((d : ℝ) / 2) (besselHankelTransform ((d : ℝ) / 2) G) +
        hankelMass ((d : ℝ) / 2) (fun Δ => (-1 : ℝ) * G Δ) := h2
  linarith

end HankelShellProfile

/-- The uniform tail bound `eq:qual-compact-tight` for the window profiles of eigenfunctions `f n` of sign `s = ±1`
with `M[f n] ≤ μ n`: for every `δ > 0` there is `b₀` such that for `b ≥ b₀` and large `n`,
`∫_{u > b} |Ψ_{f n}| / μ n ≤ δ`. -/
lemma tail_small {c μ : ℕ → ℝ} {f : ℕ → ℝ → ℝ} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hc : Tendsto c atTop atTop) (hcpos : ∀ k, 0 < c k) (hf : ∀ k, IsHankelEigenfn (c k) s (f k))
    (hμ : ∀ k, 0 < μ k) (hB : ∀ k, hankelMass (c k) (f k) ≤ μ k) :
    ∀ δ > 0, ∃ b₀ : ℝ, ∀ b ≥ b₀, ∀ᶠ n in atTop,
      ∫ u in Ioi b, |hankelWindowProfile (c n) (f n) u / μ n| ≤ δ := by
  intro δ hδ
  have t1 : Tendsto (fun x : ℝ => 8 * Real.exp (-5 * x ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (3 / 2 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h2 : Tendsto (fun x : ℝ => -5 * x ^ (3 / 2 : ℝ)) atTop atBot :=
      h1.const_mul_atTop_of_neg (by norm_num)
    simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 8
  obtain ⟨R₀, hR₀1, hR₀⟩ : ∃ R₀ : ℝ, 1 ≤ R₀ ∧ 8 * Real.exp (-5 * R₀ ^ (3 / 2 : ℝ)) ≤ δ / 2 := by
    obtain ⟨x, h1, h2⟩ := ((eventually_ge_atTop (1 : ℝ)).and
      (t1.eventually (Iic_mem_nhds (half_pos hδ)))).exists
    exact ⟨x, h1, h2⟩
  refine ⟨R₀ * hankelBeta1, fun b hb => ?_⟩
  have hβ := hankelBeta1_pos
  set R : ℝ := b / hankelBeta1 with hR
  have hRb : R * hankelBeta1 = b := by rw [hR]; field_simp
  have hR₀R : R₀ ≤ R := by rw [hR, le_div_iff₀ hβ]; exact hb
  have e1 : 8 * Real.exp (-5 * R ^ (3 / 2 : ℝ)) ≤ δ / 2 := by
    refine le_trans ?_ hR₀
    have : R₀ ^ (3 / 2 : ℝ) ≤ R ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hR₀R (by norm_num)
    have := Real.exp_le_exp.mpr (by linarith : -5 * R ^ (3 / 2 : ℝ) ≤ -5 * R₀ ^ (3 / 2 : ℝ))
    linarith
  have t2 : Tendsto (fun n => 8 * Real.exp (-(1 / 25) * c n)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => -(1 / 25) * c n) atTop atBot :=
      hc.const_mul_atTop_of_neg (by norm_num)
    simpa using (Real.tendsto_exp_atBot.comp h2).const_mul 8
  filter_upwards [hc.eventually_ge_atTop 56, t2.eventually (Iic_mem_nhds (half_pos hδ))] with n hn56 hn2
  have hc0 := hcpos n
  have hμn := hμ n
  have hdl := deep_lobe_mass_thm hn56 (hf n) hs (R := R) (by linarith)
  simp_rw [abs_div, abs_of_pos hμn]
  rw [integral_div, ← hRb, integral_tail_abs_hankelWindowProfile hc0 (f n) R, div_le_iff₀ hμn]
  refine hdl.trans ?_
  have hM0 := hankelMass_nonneg hc0 (f n)
  have hM := hB n
  have ha : 0 ≤ Real.exp (-5 * R ^ (3 / 2 : ℝ)) := (Real.exp_pos _).le
  have hb' : 0 ≤ Real.exp (-(1 / 25) * c n) := (Real.exp_pos _).le
  calc 8 * hankelMass (c n) (f n) * (Real.exp (-5 * R ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c n))
      = hankelMass (c n) (f n) * (8 * Real.exp (-5 * R ^ (3 / 2 : ℝ)) +
          8 * Real.exp (-(1 / 25) * c n)) := by ring
    _ ≤ hankelMass (c n) (f n) * δ := mul_le_mul_of_nonneg_left (by linarith) hM0
    _ ≤ μ n * δ := mul_le_mul_of_nonneg_right hM hδ.le
    _ = δ * μ n := by ring

/-- Local uniform convergence on `ℝ` to a continuous limit gives local `L¹` convergence on every `[a, b]`. -/
lemma setIntegral_Icc_abs_sub_tendsto {Φ : ℕ → ℝ → ℝ} {L : ℝ → ℝ} (hΦi : ∀ k, Integrable (Φ k))
    (hLc : Continuous L) (h : TendstoLocallyUniformlyOn Φ L atTop univ) (a b : ℝ) :
    Tendsto (fun k => ∫ u in Icc a b, |Φ k u - L u|) atTop (𝓝 0) := by
  rcases le_or_gt a b with hab | hab
  · have hU : TendstoUniformlyOn Φ L atTop (Icc a b) :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
        (h.mono (subset_univ _))
    have hU' : TendstoUniformlyOn (fun k u => |Φ k u - L u|) (fun _ => (0 : ℝ)) atTop (Icc a b) := by
      rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
      intro ε hε
      filter_upwards [hU ε hε] with k hk x hx
      have := hk x hx
      rw [Real.dist_eq] at this ⊢
      rw [abs_sub_comm] at this
      simpa using this
    have := setIntegral_Icc_tendsto_unif (g := fun k u => |Φ k u - L u|) (G := fun _ => (0 : ℝ)) hab hU'
      (Eventually.of_forall fun k =>
        ((hΦi k).integrableOn.sub hLc.continuousOn.integrableOn_Icc).abs)
      continuousOn_const.integrableOn_Icc
    simpa using this
  · have : Icc a b = ∅ := Icc_eq_empty_of_lt hab
    simp [this]

end FormalResearch.SignUncertainty
