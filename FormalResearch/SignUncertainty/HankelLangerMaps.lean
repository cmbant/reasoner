module

public import FormalResearch.SignUncertainty.HankelLangerChart
public import FormalResearch.SignUncertainty.HankelCpowBounds

/-!
# The odd maps `h` and `𝗆` of the Hankel Langer chart (`gt:7.7b` (ii))

With `G(w) = ∑ aG_j w^j = 1 + ε(w)` and `E(w) = ∑ aE_j w^j` (`HankelLangerChart`) put
`h(ζ) = ζ G(ζ²)^{1/2}` and `𝗆(ζ) = ζ E(ζ²)^{1/3}` (`gt:7.7b`: `h = z (12 g/(π² z²))^{1/2}`,
`𝗆 = z E^{1/3}`).  On `‖ζ‖ ≤ ϱ = 0.035` we prove they are differentiable, with
`‖h' - 1‖ ≤ 1.2·10⁻³` and `‖𝗆' - 1‖ ≤ 9·10⁻⁴`, using the mean-value bound `norm_one_add_cpow_sub_one_le`.
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `k(ζ) = ζ F(ζ²)^α`. -/
noncomputable def powMap (F : ℂ → ℂ) (α : ℝ) (ζ : ℂ) : ℂ := ζ * F (ζ ^ 2) ^ (α : ℂ)

/-- The derivative of `powMap F α`: `F^α + ζ α F^{α-1} F'(ζ²) 2ζ`. -/
noncomputable def powMapD (F : ℂ → ℂ) (F' : ℂ → ℂ) (α : ℝ) (ζ : ℂ) : ℂ :=
  F (ζ ^ 2) ^ (α : ℂ) +
    ζ * ((α : ℂ) * F (ζ ^ 2) ^ ((α : ℂ) - 1) * (F' (ζ ^ 2) * (2 * ζ)))

lemma hasDerivAt_powMap {F F' : ℂ → ℂ} {ζ : ℂ} (α : ℝ) (hF : HasDerivAt F (F' (ζ ^ 2)) (ζ ^ 2))
    (hslit : F (ζ ^ 2) ∈ slitPlane) :
    HasDerivAt (powMap F α) (powMapD F F' α ζ) ζ := by
  have h2 : HasDerivAt (fun ζ : ℂ => ζ ^ 2) (2 * ζ) ζ := by
    simpa using hasDerivAt_pow 2 ζ
  have hF' : HasDerivAt F (F' (ζ ^ 2)) ((fun ζ : ℂ => ζ ^ 2) ζ) := hF
  have hc : HasDerivAt (fun ζ : ℂ => F (ζ ^ 2)) (F' (ζ ^ 2) * (2 * ζ)) ζ :=
    HasDerivAt.comp (h₂ := F) (h := fun ζ : ℂ => ζ ^ 2) ζ hF' h2
  have hp := hc.cpow_const (c := (α : ℂ)) hslit
  have := (hasDerivAt_id ζ).mul hp
  have hfun : powMap F α = (id * fun x : ℂ => F (x ^ 2) ^ (α : ℂ)) := by
    funext x; simp [powMap]
  rw [hfun]
  convert this using 1
  simp [powMapD]

/-- Generic bound `‖k' - 1‖ ≤ α τ/(1-τ) + 2 α r² D/(1-τ)`. -/
lemma norm_powMapD_sub_one_le {F F' : ℂ → ℂ} {ζ : ℂ} {α τ D : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hτ : τ < 1) (hx : ‖F (ζ ^ 2) - 1‖ ≤ τ) (hD : ‖F' (ζ ^ 2)‖ ≤ D) :
    ‖powMapD F F' α ζ - 1‖ ≤ α * τ / (1 - τ) + 2 * α * ‖ζ‖ ^ 2 * D / (1 - τ) := by
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hx
  have h1 : 0 < 1 - τ := by linarith
  have hx' : ‖F (ζ ^ 2) - 1‖ ≤ τ := hx
  have hF : F (ζ ^ 2) = 1 + (F (ζ ^ 2) - 1) := by ring
  have hA := norm_one_add_cpow_sub_one_le hα hα1 hx' hτ
  rw [← hF] at hA
  have hB := norm_one_add_cpow_neg_le (γ := 1 - α) (by linarith) (by linarith) hx' hτ
  rw [← hF] at hB
  have e : (((-(1 - α) : ℝ)) : ℂ) = (α : ℂ) - 1 := by push_cast; ring
  rw [e] at hB
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hD
  unfold powMapD
  have : F (ζ ^ 2) ^ (α : ℂ) + ζ * ((α : ℂ) * F (ζ ^ 2) ^ ((α : ℂ) - 1) * (F' (ζ ^ 2) * (2 * ζ))) - 1
      = (F (ζ ^ 2) ^ (α : ℂ) - 1) +
        ζ * ((α : ℂ) * F (ζ ^ 2) ^ ((α : ℂ) - 1) * (F' (ζ ^ 2) * (2 * ζ))) := by ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add hA ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [hn2]
  have hζ : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  calc ‖ζ‖ * (α * ‖F (ζ ^ 2) ^ ((α : ℂ) - 1)‖ * (‖F' (ζ ^ 2)‖ * (2 * ‖ζ‖)))
      ≤ ‖ζ‖ * (α * (1 / (1 - τ)) * (D * (2 * ‖ζ‖))) := by gcongr
    _ = 2 * α * ‖ζ‖ ^ 2 * D / (1 - τ) := by field_simp


section Chart

variable {η : ℕ → ℝ}

/-- `h(ζ) = ζ (12 g(ζ)/(π² ζ²))^{1/2}`. -/
noncomputable def hMap (η : ℕ → ℝ) : ℂ → ℂ := powMap (psW (aG η)) (1 / 2)

/-- `𝗆(ζ) = ζ E(ζ²)^{1/3}`. -/
noncomputable def mMap (η : ℕ → ℝ) : ℂ → ℂ := powMap (psW (aE η)) (1 / 3)

lemma div_one_sub_mono {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) (hq : q < 1) :
    r / (1 - r) ≤ q / (1 - q) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma norm_sq_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) : ‖ζ ^ 2‖ ≤ 0.035 ^ 2 := by
  rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hζ 2

lemma norm_psWaG_sub_one_le (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    ‖psW (aG η) (ζ ^ 2) - 1‖ ≤ 7.46e-4 := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have := norm_chartEps_le h h1
  unfold chartEps at this
  refine this.trans ?_
  have hm := div_one_sub_mono (norm_nonneg (ζ ^ 2)) hw (by norm_num : (0.035 : ℝ) ^ 2 < 1)
  calc 6 / π ^ 2 * ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖) = 6 / π ^ 2 * (‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖)) := by ring
    _ ≤ 6 / π ^ 2 * (0.035 ^ 2 / (1 - 0.035 ^ 2)) := by gcongr
    _ = 6 / π ^ 2 * (0.035 ^ 2) / (1 - 0.035 ^ 2) := by ring
    _ ≤ 7.46e-4 := chartEpsH_le

lemma norm_psWaE_sub_one_le (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    ‖psW (aE η) (ζ ^ 2) - 1‖ ≤ 8.95e-4 := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have := norm_chartE_sub_one_le h h1
  unfold chartE at this
  refine this.trans ?_
  have hm := div_one_sub_mono (norm_nonneg (ζ ^ 2)) hw (by norm_num : (0.035 : ℝ) ^ 2 < 1)
  calc 36 / (5 * π ^ 2) * ‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖)
        = 36 / (5 * π ^ 2) * (‖ζ ^ 2‖ / (1 - ‖ζ ^ 2‖)) := by ring
    _ ≤ 36 / (5 * π ^ 2) * (0.035 ^ 2 / (1 - 0.035 ^ 2)) := by gcongr
    _ = 36 / (5 * π ^ 2) * (0.035 ^ 2) / (1 - 0.035 ^ 2) := by ring
    _ ≤ 8.95e-4 := chartEpsE_le

lemma hasDerivAt_hMap (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    HasDerivAt (hMap η) (powMapD (psW (aG η)) (psWD (aG η)) (1 / 2) ζ) ζ := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hd : HasDerivAt (psW (aG η)) (psWD (aG η) (ζ ^ 2)) (ζ ^ 2) :=
    hasDerivAt_psW (B := 1) (abs_aG_le_one h) h1
  have hx := norm_psWaG_sub_one_le h hζ
  have hs : psW (aG η) (ζ ^ 2) ∈ slitPlane := by
    have := one_add_mem_slitPlane (y := psW (aG η) (ζ ^ 2) - 1) (lt_of_le_of_lt hx (by norm_num))
    simpa using this
  exact hasDerivAt_powMap (F := psW (aG η)) (F' := psWD (aG η)) (1 / 2) hd hs

lemma hasDerivAt_mMap (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    HasDerivAt (mMap η) (powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) ζ) ζ := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hd : HasDerivAt (psW (aE η)) (psWD (aE η) (ζ ^ 2)) (ζ ^ 2) :=
    hasDerivAt_psW (B := 1) (abs_aE_le_one h) h1
  have hx := norm_psWaE_sub_one_le h hζ
  have hs : psW (aE η) (ζ ^ 2) ∈ slitPlane := by
    have := one_add_mem_slitPlane (y := psW (aE η) (ζ ^ 2) - 1) (lt_of_le_of_lt hx (by norm_num))
    simpa using this
  exact hasDerivAt_powMap (F := psW (aE η)) (F' := psWD (aE η)) (1 / 3) hd hs

/-- `‖h' - 1‖ ≤ 1.2·10⁻³` on `‖ζ‖ ≤ 0.035` (`gt:7.7b` (ii)). -/
lemma norm_hMapD_sub_one_le (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    ‖powMapD (psW (aG η)) (psWD (aG η)) (1 / 2) ζ - 1‖ ≤ 1.2e-3 := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hx := norm_psWaG_sub_one_le h hζ
  have hD0 := norm_deriv_chartEps_le h h1
  have hp : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hP : 6 / π ^ 2 ≤ 6 / 9.869 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp.le
  have hDq : ‖psWD (aG η) (ζ ^ 2)‖ ≤ (6 / 9.869) / (1 - 0.035 ^ 2) ^ 2 := by
    refine hD0.trans ?_
    have : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖ζ ^ 2‖ := by linarith
    have h2 : (1 - 0.035 ^ 2 : ℝ) ^ 2 ≤ (1 - ‖ζ ^ 2‖) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) this
    calc 6 / π ^ 2 / (1 - ‖ζ ^ 2‖) ^ 2 ≤ 6 / π ^ 2 / (1 - 0.035 ^ 2) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
      _ ≤ (6 / 9.869) / (1 - 0.035 ^ 2) ^ 2 := by gcongr
  have := norm_powMapD_sub_one_le (F := psW (aG η)) (F' := psWD (aG η)) (ζ := ζ) (α := 1 / 2)
    (τ := 7.46e-4) (D := (6 / 9.869) / (1 - 0.035 ^ 2) ^ 2) (by norm_num) (by norm_num)
    (by norm_num) hx hDq
  refine this.trans ?_
  have hz2 : ‖ζ‖ ^ 2 ≤ 0.035 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have : 2 * (1 / 2 : ℝ) * ‖ζ‖ ^ 2 * ((6 / 9.869) / (1 - 0.035 ^ 2) ^ 2) / (1 - 7.46e-4)
      ≤ 2 * (1 / 2 : ℝ) * 0.035 ^ 2 * ((6 / 9.869) / (1 - 0.035 ^ 2) ^ 2) / (1 - 7.46e-4) := by
    gcongr
  refine le_trans (add_le_add le_rfl this) ?_
  norm_num

/-- `‖𝗆' - 1‖ ≤ 9·10⁻⁴` on `‖ζ‖ ≤ 0.035` (`gt:7.7b` (ii)). -/
lemma norm_mMapD_sub_one_le (h : LangerEta η) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 0.035) :
    ‖powMapD (psW (aE η)) (psWD (aE η)) (1 / 3) ζ - 1‖ ≤ 9e-4 := by
  have hw := norm_sq_le hζ
  have h1 : ‖ζ ^ 2‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hx := norm_psWaE_sub_one_le h hζ
  have hD0 := norm_deriv_chartE_le h h1
  have hp : (9.869 : ℝ) < π ^ 2 := by nlinarith [Real.pi_gt_d4]
  have hP : 36 / (5 * π ^ 2) ≤ 36 / (5 * 9.869) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hDq : ‖psWD (aE η) (ζ ^ 2)‖ ≤ (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2 := by
    refine hD0.trans ?_
    have : (1 - 0.035 ^ 2 : ℝ) ≤ 1 - ‖ζ ^ 2‖ := by linarith
    have h2 : (1 - 0.035 ^ 2 : ℝ) ^ 2 ≤ (1 - ‖ζ ^ 2‖) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) this
    calc 36 / (5 * π ^ 2) / (1 - ‖ζ ^ 2‖) ^ 2 ≤ 36 / (5 * π ^ 2) / (1 - 0.035 ^ 2) ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) h2
      _ ≤ (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2 := by gcongr
  have := norm_powMapD_sub_one_le (F := psW (aE η)) (F' := psWD (aE η)) (ζ := ζ) (α := 1 / 3)
    (τ := 8.95e-4) (D := (36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) (by norm_num) (by norm_num)
    (by norm_num) hx hDq
  refine this.trans ?_
  have hz2 : ‖ζ‖ ^ 2 ≤ 0.035 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have : 2 * (1 / 3 : ℝ) * ‖ζ‖ ^ 2 * ((36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) / (1 - 8.95e-4)
      ≤ 2 * (1 / 3 : ℝ) * 0.035 ^ 2 * ((36 / (5 * 9.869)) / (1 - 0.035 ^ 2) ^ 2) / (1 - 8.95e-4) := by
    gcongr
  refine le_trans (add_le_add le_rfl this) ?_
  norm_num

end Chart

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_hMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hMap

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_mMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_mMap

/-- info: 'FormalResearch.SignUncertainty.norm_hMapD_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hMapD_sub_one_le

/-- info: 'FormalResearch.SignUncertainty.norm_mMapD_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mMapD_sub_one_le

end FormalResearch.SignUncertainty
