module

public import FormalResearch.SignUncertainty.HankelBootMultilevel
public import FormalResearch.ModularBootstrap.FoldTip.HankelChartCompactness

/-!
# Multilevel Cohn–Elkies Shell Reduction (`thm:ce-shell-reduction`, `R2d`)

Derives `ShellReduction D` at every Hermite–Biehler configuration `D : ShellHBData` from
`hbMultilevelLower_proved D` via the Euclidean-to-Hankel radial projection
`shellAdmissible_isHankelPrescribed` (`ModularBootstrap.FoldTip.HankelChartCompactness`),
discharging the last field `shell_reduction` of `CeCanonicalInputs`.
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.ModularBootstrap.FoldTip

private lemma hankelSites_nonneg_of_large (D : ShellHBData) (R_off : ℝ) :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∀ r : ℝ → ℝ → ℝ, (∀ t c', |r t c'| ≤ R_off) →
      ∀ s ∈ hankelSites D r c, 0 < s := by
  let A : ℝ := ∑ t ∈ D.S, |t| / hankelBeta1
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => div_nonneg (abs_nonneg _) hankelBeta1_pos.le
  let c₀ : ℝ := max 1 (π ^ 2 * (A + max R_off 0 + 1)) ^ 3
  refine ⟨max 1 c₀, le_max_left _ _, fun c hc r hr s hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have htS : t ∈ D.S := (Finset.mem_erase.mp ht).2
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc_ge : c₀ ≤ c := (le_max_right _ _).trans hc
  have hc13 : max 1 (π ^ 2 * (A + max R_off 0 + 1)) ≤ c ^ (1 / 3 : ℝ) := by
    have h1 : max 1 (π ^ 2 * (A + max R_off 0 + 1)) ^ (3 : ℝ) ≤ c := by exact_mod_cast hc_ge
    calc max 1 (π ^ 2 * (A + max R_off 0 + 1))
        = (max 1 (π ^ 2 * (A + max R_off 0 + 1)) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hpow2 : π ^ 2 * (A + max R_off 0 + 1) ≤ (c ^ (1 / 3 : ℝ)) ^ 2 := by
    have h1 : π ^ 2 * (A + max R_off 0 + 1) ≤ c ^ (1 / 3 : ℝ) := (le_max_right _ _).trans hc13
    have h2 : 1 ≤ c ^ (1 / 3 : ℝ) := (le_max_left _ _).trans hc13
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ c ^ (1 / 3 : ℝ))]
  have hpi : 0 < π ^ 2 := by positivity
  have hdom : A + max R_off 0 + 1 ≤ c ^ (2 / 3 : ℝ) / π ^ 2 := by
    rw [le_div_iff₀ hpi]
    have hpow23 : c ^ (2 / 3 : ℝ) = (c ^ (1 / 3 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num
    rw [hpow23]
    linarith
  have hc_dom : (A + max R_off 0 + 1) * c ^ (1 / 3 : ℝ) ≤ c / π ^ 2 := by
    calc (A + max R_off 0 + 1) * c ^ (1 / 3 : ℝ)
        ≤ (c ^ (2 / 3 : ℝ) / π ^ 2) * c ^ (1 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hdom (Real.rpow_nonneg hc0.le _)
      _ = (c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) / π ^ 2 := by ring
      _ = c / π ^ 2 := by rw [← Real.rpow_add hc0]; norm_num
  have hle : |t| / hankelBeta1 ≤ A :=
    Finset.single_le_sum (f := fun s => |s| / hankelBeta1)
      (fun _ _ => div_nonneg (abs_nonneg _) hankelBeta1_pos.le) htS
  have h2 : t / hankelBeta1 ≤ A :=
    (div_le_div_of_nonneg_right (le_abs_self t) hankelBeta1_pos.le).trans hle
  have h1c : 1 ≤ c ^ (1 / 3 : ℝ) := (le_max_left _ _).trans hc13
  have h5 := (abs_le.mp (hr t c)).1
  have h_off : -r t c ≤ max R_off 0 * c ^ (1 / 3 : ℝ) := by
    calc -r t c ≤ R_off := by linarith
      _ ≤ max R_off 0 := le_max_left _ _
      _ ≤ max R_off 0 * c ^ (1 / 3 : ℝ) := le_mul_of_one_le_right (le_max_right _ _) h1c
  unfold hankelLevel
  nlinarith [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hc0.le (1 / 3 : ℝ)),
    Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)]

/-- **`thm:ce-shell-reduction`** at every Hermite–Biehler configuration `D : ShellHBData`:
for every `R_off ≥ 0`, any admissible Cohn–Elkies shell profile at bounded offsets `|r t d'| ≤ R_off`
satisfies `R²/2 ≥ d/(2π²) - (t_m/β₁)(d/2)^{1/3} - C` for all large `d`. -/
theorem shellReduction_proved (D : ShellHBData) : ShellReduction D := by
  intro R_off hR
  obtain ⟨C, c₀, hlow⟩ := hbMultilevelLower_proved D R_off hR
  obtain ⟨c₁, _, hpos⟩ := hankelSites_nonneg_of_large D R_off
  let d₀ : ℕ := max 2 (⌈2 * max c₀ c₁⌉₊)
  refine ⟨C, d₀, fun d hd r hr R hRmem => ?_⟩
  have hd2 : 2 ≤ d := le_trans (le_max_left _ _) hd
  have hd_ceil : (⌈2 * max c₀ c₁⌉₊ : ℝ) ≤ d := by
    exact_mod_cast le_trans (le_max_right _ _) hd
  have hc_max : max c₀ c₁ ≤ (d : ℝ) / 2 := by
    have := Nat.le_ceil (2 * max c₀ c₁)
    linarith
  have hc₀ : c₀ ≤ (d : ℝ) / 2 := (le_max_left _ _).trans hc_max
  have hc₁ : c₁ ≤ (d : ℝ) / 2 := (le_max_right _ _).trans hc_max
  obtain ⟨h, hadm⟩ := hRmem
  have hsites : ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) d := fun t htS htne => by
    have hs := hpos ((d : ℝ) / 2) hc₁ (fun t _ => r t d) (fun t _ => hr t d)
      (hankelLevel t ((d : ℝ) / 2) (r t d))
      (Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨htne, htS⟩, rfl⟩)
    have heq : shellSite t (r t) d = hankelLevel t ((d : ℝ) / 2) (r t d) := by
      unfold shellSite hankelLevel; rw [div_div]
    rw [heq]
    exact hs.le
  obtain ⟨G, hG, -⟩ := shellAdmissible_isHankelPrescribed hd2 hadm hsites
  have hbound := hlow ((d : ℝ) / 2) hc₀ (-1) (Or.inr rfl) (fun t _ => r t d)
    (fun t _ => hr t d) (R ^ 2 / 2) G hG
  have hmod : hbModel D ((d : ℝ) / 2) =
      (d : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((d : ℝ) / 2) ^ (1 / 3 : ℝ) := by
    unfold hbModel; rw [div_div]
  linarith only [hbound, hmod]

/-- info: 'FormalResearch.SignUncertainty.shellReduction_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellReduction_proved

end FormalResearch.SignUncertainty
