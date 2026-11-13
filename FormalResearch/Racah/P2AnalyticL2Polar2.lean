module

public import FormalResearch.Racah.P2AnalyticL2Polar
public import FormalResearch.Racah.P2AnalyticL2Transmutation
public import FormalResearch.Racah.P2HahnKernel

/-!
# The physical gauges and `eq:SNpolar` (Weyl P2, `prop:betabinomialpolar`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:betabinomialpolar` (`eq:SNpolar`),
Appendix `app:beta-polar` (`eq:GcGauge`-`eq:physicalGaugeModes`).

* `Gd`: the gauge `G_d` (`eq:GdGauge`), `Gd_ipN` its isometry into `ℓ²(𝒳_N, 2h)`;
* `vN_eq_Gd`: `v_L = (-1)^α G_d H_n` (`eq:physicalGaugeModes`, discrete half), from `eq:ExactHahnKernel`
  (`Phi3j_hahn`) and `sqrt_pD_Hmode : √p_D H_n = √(w_H/h_n) Q_n`.
-/

@[expose] public section

namespace FormalResearch.Racah

open MeasureTheory Polar FormalResearch.Special FormalResearch.Wigner
open scoped InnerProductSpace

/-! ### The discrete gauge `G_d` -/

/-- **`eq:GdGauge`**: `(G_d q)(x_u) = √(N/2) p_D(u)^{1/2} q(u)`, in the coordinates
`ℓ²(p_D) ≅ ℝ^{D+1}`, `w_u = √p_D(u) q(u)`.  The lattice point `x_n = xLat M σ N n` of the code
(counted from the lower end) is `x_u` with `u = D - n` (the paper measures from the upper
endpoint, `eq:HahnGridPaper`). -/
noncomputable def Gd (N : ℚ) (D K : ℕ) : EuclideanSpace ℝ (Fin (D + 1)) →ₗ[ℝ] (Fin K → ℝ) where
  toFun w := fun n => Real.sqrt ((N : ℝ) / 2) * w ⟨D - n, by omega⟩
  map_add' x y := by funext n; simp [mul_add]
  map_smul' c x := by funext n; simp; ring

lemma Gd_apply (N : ℚ) (D K : ℕ) (w : EuclideanSpace ℝ (Fin (D + 1))) (n : Fin K) :
    Gd N D K w n = Real.sqrt ((N : ℝ) / 2) * w ⟨D - n, by omega⟩ := rfl

/-- `G_d` in the function form of `eq:GdGauge`: `G_d q = G_d (√p_D q)`. -/
theorem Gd_wvec (α β D K : ℕ) (N : ℚ) (q : ℕ → ℝ) (n : Fin K) :
    Gd N D K (wvec α β D q) n =
      Real.sqrt ((N : ℝ) / 2) * Real.sqrt (pD α β D (D - n)) * q (D - n) := by
  rw [Gd_apply]; simp only [wvec]; ring

/-- **`G_d` is isometric** `ℓ²(p_D) → ℓ²(𝒳_N, 2h)`: `⟨G_d w, G_d w'⟩_{2h} = ⟨w, w'⟩`. -/
theorem Gd_ipN (N : ℚ) (hN : 0 < N) (D : ℕ) (w w' : EuclideanSpace ℝ (Fin (D + 1))) :
    ipN N (Gd N D (D + 1) w) (Gd N D (D + 1) w') = ⟪w, w'⟫_ℝ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold ipN
  have e : ∀ n : Fin (D + 1), Gd N D (D + 1) w n * Gd N D (D + 1) w' n =
      ((N : ℝ) / 2) * (w (Fin.rev n) * w' (Fin.rev n)) := by
    intro n
    have h : (⟨D - n, by omega⟩ : Fin (D + 1)) = Fin.rev n := Fin.ext (by simp [Fin.val_rev])
    have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ (N : ℝ) / 2 by positivity)
    rw [Gd_apply, Gd_apply, h]
    linear_combination (w (Fin.rev n) * w' (Fin.rev n)) * hs
  simp only [e]
  have hrev : ∑ i : Fin (D + 1), w (Fin.rev i) * w' (Fin.rev i) = ∑ i : Fin (D + 1), w i * w' i :=
    Equiv.sum_comp Fin.revPerm (fun n => w n * w' n)
  rw [← Finset.mul_sum, hrev]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have : ∑ x : Fin (D + 1), w' x * w x = ∑ x : Fin (D + 1), w x * w' x :=
    Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [this]
  field_simp

/-! ### `√p_D H_n` is the Hahn kernel -/

lemma sqrt_pD_Hmode (α β D n u : ℕ) (hu : u ≤ D) :
    Real.sqrt (pD α β D u) * Hmode α β D n u =
      Real.sqrt ((hahnW α β D u : ℝ) / hahnNorm α β D n) * hahnQ α β D n u := by
  have hC : (0 : ℝ) < ((α + β + 1 + D).choose D : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hh := hahnNorm_pos α β D n
  have hw : (0 : ℝ) ≤ hahnW α β D u := by positivity
  have e1 : ipP α β D (hahnQ α β D n) (hahnQ α β D n) = hahnNorm α β D n /
      ((α + β + 1 + D).choose D : ℝ) := by
    rw [ipP_hahnQ_eq]; unfold hahnNorm; congr 1
    exact Finset.sum_congr rfl fun v _ => by ring
  unfold Hmode
  rw [e1, pD_eq_hahnW α β D u hu, Real.sqrt_div' _ hC.le, Real.sqrt_div' _ hC.le,
    Real.sqrt_div' _ hh.le]
  have h1 : 0 < Real.sqrt (hahnNorm α β D n) := Real.sqrt_pos.2 hh
  have h2 : 0 < Real.sqrt ((α + β + 1 + D).choose D : ℝ) := Real.sqrt_pos.2 hC
  field_simp


/-- **`v_L = (-1)^{α_H} G_d H_n`** (`eq:physicalGaugeModes`, discrete half): in the chamber `M ≥ |σ|`
(`α = M-σ`, `β = M+σ`, `D = N-M-1`, `n = L-M`), the exact `3j` mode `v_L = vN n` equals
`(-1)^α G_d H_n`.  This is `eq:ExactHahnKernel` (`Phi3j_hahn`) with `√p_D H_n = √(w_H/h_n) Q_n`. -/
theorem vN_eq_Gd {M σ N : ℚ} {α β D : ℕ} (hα : M - σ = α) (hβ : M + σ = β)
    (hD : N - M - 1 = D) (n : Fin (D + 1)) :
    vN M σ N (K := D + 1) n = ((-1 : ℝ) ^ α) • Gd N D (D + 1) (HB α β D n) := by
  funext n'
  have hNq : 0 < N := by
    have h1 : (0 : ℚ) ≤ α := Nat.cast_nonneg _
    have h2 : (0 : ℚ) ≤ β := Nat.cast_nonneg _
    have h3 : (0 : ℚ) ≤ D := Nat.cast_nonneg _
    linarith
  have hmax := chamber_max hα hβ
  have hn' : (n' : ℕ) ≤ D := by omega
  have hnD : (n : ℕ) ≤ D := by omega
  have hM0 : (0 : ℝ) ≤ M := by
    have : (0 : ℚ) ≤ M := by
      have h1 : (0 : ℚ) ≤ α := Nat.cast_nonneg _
      have h2 : (0 : ℚ) ≤ β := Nat.cast_nonneg _
      linarith
    exact_mod_cast this
  have hPhi : PhiX (rkN M σ n) M σ N (xLat M σ N n') =
      (-1 : ℝ) ^ α * Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + (n : ℕ)) + 1)) *
        Real.sqrt ((hahnW α β D (D - n') : ℝ) / hahnNorm α β D n) * hahnQ α β D n (D - n') := by
    unfold PhiX rkN
    rw [mu_lat M σ N hNq.ne' n', hmax]
    exact Phi3j_hahn hα hβ hD n (D - n') hnD (lat_u hα hβ hD n' hn') (by omega)
  unfold vN
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hPhi, Gd_apply, HB_coe]
  have hHW : (HW α β D n) ⟨D - n', by omega⟩ =
      Real.sqrt (pD α β D (D - n')) * Hmode α β D n (D - n') := by
    simp [HW, wvec]
  rw [hHW, sqrt_pD_Hmode α β D n (D - n') (by omega)]
  have hL : (0 : ℝ) < 2 * ((M : ℝ) + (n : ℕ)) + 1 := by positivity
  have hrk : (((rkN M σ n : ℚ)) : ℝ) = (M : ℝ) + (n : ℕ) := by
    unfold rkN; rw [hmax]; push_cast; ring
  rw [hrk]
  have key : Real.sqrt ((2 * ((M : ℝ) + (n : ℕ)) + 1) / 2) *
      Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + (n : ℕ)) + 1)) = Real.sqrt ((N : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  linear_combination ((-1 : ℝ) ^ α * Real.sqrt ((hahnW α β D (D - n') : ℝ) / hahnNorm α β D n) *
    hahnQ α β D n (D - n')) * key

/-- info: 'FormalResearch.Racah.Gd_ipN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gd_ipN

/-- info: 'FormalResearch.Racah.vN_eq_Gd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms vN_eq_Gd

end FormalResearch.Racah
