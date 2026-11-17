module

public import FormalResearch.Special.LatticeConcrete

/-!
# The density of levels `G'/π`: pointwise facts

`gdens nc ℓ s = (ℓ - nc Re ψ(½+is))/π` is `t₀'(s) = G'(s)/π` (`realDeriv_gamma`), continuous, with
`|gdens s| ≤ (ℓ + 5nc)/π + (nc/π)|s|` when `ℓ ≥ 0` (from `Re ψ ≥ -3`, `Re ψ ≤ log(1+|s|)+5`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes

/-- `G'(s)/π = (ℓ - nc Re ψ(½+is))/π`. -/
noncomputable def gdens (nc : ℕ) (ℓ s : ℝ) : ℝ := (ℓ - nc * (digamma (1 / 2 + I * s)).re) / Real.pi

lemma realDeriv_gamma (nc : ℕ) (ℓ θ0 s : ℝ) :
    CalPhase.realDeriv (gammaPhase nc ℓ θ0) s = gdens nc ℓ s := by
  unfold CalPhase.realDeriv gdens
  rw [deriv_gammaPhase nc ℓ θ0 (by simp), Complex.div_ofReal_re, phaseDeriv_real]
  simp

lemma continuous_gdens (nc : ℕ) (ℓ : ℝ) : Continuous (gdens nc ℓ) := by
  have hd : Continuous (fun s : ℝ => digamma (1 / 2 + I * s)) := by
    have h1 : ContinuousOn digamma rhp := differentiableOn_digamma_rhp.continuousOn
    have h2 : Continuous (fun s : ℝ => (1 / 2 : ℂ) + I * s) := by fun_prop
    exact h1.comp_continuous h2 (fun s => by show 0 < ((1 / 2 : ℂ) + I * s).re; simp)
  unfold gdens
  have : Continuous (fun s : ℝ => (digamma (1 / 2 + I * s)).re) := Complex.continuous_re.comp hd
  fun_prop

lemma abs_gdens_le (nc : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (s : ℝ) :
    |gdens nc ℓ s| ≤ (ℓ + 5 * nc) / Real.pi + nc / Real.pi * |s| := by
  unfold gdens
  have hpi := Real.pi_pos
  have lo := re_digamma_half_line_ge s
  have up := re_digamma_upper (x := 1 / 2) (y := s) (by norm_num) (by norm_num)
  have e1 : (1 / 2 + (s : ℂ) * I) = 1 / 2 + I * s := by ring
  have e2 : (((1 / 2 : ℝ) : ℂ) + (s : ℂ) * I) = 1 / 2 + I * s := by push_cast; ring
  rw [e1] at lo
  rw [e2] at up
  have hlog : Real.log (1 + |s|) ≤ |s| := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |s|); linarith
  set R := (digamma (1 / 2 + I * s)).re
  have hnc : (0 : ℝ) ≤ nc := Nat.cast_nonneg nc
  rw [abs_div, abs_of_pos hpi, div_le_iff₀ hpi, abs_le]
  have h1 : ℓ - nc * R ≤ ℓ + 5 * nc + nc * |s| := by nlinarith [abs_nonneg s]
  have h2 : -(ℓ + 5 * nc + nc * |s|) ≤ ℓ - nc * R := by nlinarith [abs_nonneg s]
  have e : ((ℓ + 5 * nc) / Real.pi + nc / Real.pi * |s|) * Real.pi = ℓ + 5 * nc + nc * |s| := by
    field_simp
  rw [e]
  exact ⟨h2, h1⟩

end FormalResearch.Special.Lattice
