module

public import FormalResearch.JE.JEVolterra

/-!
# Paper J engine, JE5: multi-patch Casoratian--Volterra stability (`thm:eng-volterra`(a), both seeds)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, Section 2 (`thm:eng-volterra`(a) and the proof
`app:eng-twopatch` in `app_engine.tex`).  Namespace `FormalResearch.JE`; builds on `JECasoratian` (Abel, Cramer),
`JEKernel` (`lem:eng-kernel`, used through its summand bounds) and `JEVolterra` (`Lh`, `Lop_eq_h_mul_Lh`).

## Statement formalised: `volterra_multi`
* Breakpoints `jj : ℕ → ℤ`, `jj 0 = 0`, strictly increasing, `jj P = N_R - 1`.  Patch `p ∈ [1,P]` has window
  `[jj (p-1), jj p + 1]` and equation sites `I_p° = [eqLo s₀ jj p, jj p]`, where `eqLo = s₀` for `p = 1` and
  `jj (p-1) + 1` for `p ≥ 2`.  The seed `s₀ ∈ {0,1}`: `s₀ = 0` is the hard edge (`A(-1) = 0`, seed `ψ₀`,
  `I° = [0, N_R-1]`); `s₀ = 1` is the two-node seed (seed `ψ₀, ψ₁`, `I° = [1, N_R-1]`).
* (S1) `c₋ ω ≤ |𝒲_j(φ¹_p, φ²_p)|` on the bonds `[jj (p-1), jj p]` (the upper bound `c₊` is not used; omitted).
* (S2) one envelope family `M, W` on the sites `[0, N_R]`, `W` non-decreasing up to `C_E`; `|φ¹_{p,j}| ≤ K W_j M_j`,
  `|φ²_{p,j}| ≤ K W_j^{-1} M_j` on the windows; `|r¹_{p,k}| ≤ ε ρ_k W_k M_k`, `|r²_{p,k}| ≤ ε ρ_k W_k^{-1} M_k` on
  `I_p°` except `r²_{1,0}` (`k = 0`, hard edge).
* (S3) `Λ⁻¹ ≤ |det M_p|`, `|M_{11}|, |M_{22}| ≤ Λ`, `|M_{12}| ≤ Λ W_{j_p}^{-2}`, `|M_{21}| ≤ Λ W_{j_p}^2` (the
  `(i,j)` entries of `M_p = transMat p`, `i,j ∈ {0,1}` in Lean).
* `c₁ = (1,0)`, `c_{p+1} = M_p c_p` (`cvec`), `ψ̂_{p,j} = c_{p,1} φ¹_{p,j} + c_{p,2} φ²_{p,j}` (`psiHat`),
  `Θ = (h/ω) ∑_p ∑_{k ∈ I_p°} ρ_k M_k²` (`volTheta`), smallness `ε Θ ≤ c*`.
* Conclusions: `|ψ_j - ψ̂_{p,j}| ≤ C ε Θ W_j M_j` on each window; `ψ̂_p = ψ̂_{p+1}` on each overlap bond (single-valuedness);
  and, for every `j ∈ [0, N_R]`, a patch `p` with the same bound.
* Constants (explicit): `D = (1+C_E²)/c₋`, `κ = 2Λ²(1+C_E²)`, `C_r* = (Λ(1+C_E²))^P (1+C_E²)`,
  `c* = 1/(2DK+1)`, `C = 2DK²C_r*((κ+1)^P + 1)`.  They depend only on `P, K, c₋, C_E, Λ`.

## Differences from the paper (all stated in the report)
1. **Transfer matrix indices.** The paper writes `M_p := U_{p+1}⁻¹ U_p` with `U_q` the rows of patch `q` at `j_q`; the
   overlap bond of patches `p, p+1` is `j_p`, so the two factors must be read at the same bond.  Formalised as
   `M_p = (bondMat (p+1) (j_p))⁻¹ · bondMat p (j_p)` (`transMat`): the change of basis on the bond `j_p`.
2. **Envelopes.** Formalised with one envelope family `M, W` on all sites (the first clause of (S2)); the paper's
   patch-dependent envelopes, comparable on overlaps, are not formalised (a special case, hence weaker).
3. **Upper Casoratian bound** `c₊` is not used by the proof and is omitted.
4. **Entry flux.** The paper's `|f¹_p| ≤ a_p ω W_{j_{p-1}}²` is formalised with a weight `V_p`, `V_1 = 0` (the flux of
   patch 1 vanishes by the seed), `V_p = W_{j_{p-1}}` otherwise; the same content.
5. **Constants** are the explicit values above, not an existential `∃ c*, C`.
6. The solution `ψ` is a hypothesis (`L_h ψ = 0` on `I°`); existence is not claimed.

## Non-vacuity
`volterra_multi_instance`: two patches, two-node seed, `A = 1`, `Q = 2cos θ`, the exact pair `cos(iθ), sin(iθ)` on both
patches (`M_p = I`), `ε = 0`, `ψ = φ¹`; every hypothesis is checked (`sin θ ≠ 0`).

Not formalised: the hard-edge instance, patch-dependent envelopes, perturbed multi-patch instances, `thm:eng-volterra`(b)
(see `JEVolterraLadder`).
-/

@[expose] public section

open Finset

namespace FormalResearch.JE

/-- The Volterra step of one patch: the telescoped Abel identity from the first equation site `s` (entry bond
`s - 1`) to the bond `m - 1`. -/
theorem flux_telescope (h : ℝ) (hh : h ≠ 0) (A Q e φ rt : ℤ → ℝ) (s m : ℤ) (hsm : s - 1 ≤ m - 1)
    (hLe : ∀ k ∈ Icc s (m - 1), Lop A Q e k = -(h * rt k)) :
    cas A e φ (m - 1) = cas A e φ (s - 1)
      - h * ∑ k ∈ Icc s (m - 1), (φ k * rt k + e k * Lh h A Q φ k) := by
  have hab := abel_sum A Q e φ s (m - 1) (by omega)
  have hterm : ∀ j ∈ Icc s (m - 1), φ j * Lop A Q e j - e j * Lop A Q φ j
      = -h * (φ j * rt j + e j * Lh h A Q φ j) := by
    intro j hj
    rw [hLe j hj, Lop_eq_h_mul_Lh h hh A Q φ j]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hab
  linarith [hab]

/-- Summand bound, the `rt`-term: `|(φ¹_m φ²_k - φ²_m φ¹_k) rt_k| ≤ (1+C_E²) K² C_r ε ρ_k M_k² W_m M_m`. -/
theorem summand_A (CE K Cr ε ρk Wm Mm Wk Mk p1m p2m p1k p2k rt : ℝ)
    (hCE : 0 ≤ CE) (hK : 0 ≤ K) (hCr : 0 ≤ Cr) (hε : 0 ≤ ε) (hρ : 0 ≤ ρk)
    (hWm : 0 < Wm) (hWk : 0 < Wk) (hMm : 0 ≤ Mm) (hMk : 0 ≤ Mk) (hkm : Wk ≤ CE * Wm)
    (h1m : |p1m| ≤ K * Wm * Mm) (h2m : |p2m| ≤ K * Wm⁻¹ * Mm)
    (h1k : |p1k| ≤ K * Wk * Mk) (h2k : |p2k| ≤ K * Wk⁻¹ * Mk)
    (hrt : |rt| ≤ Cr * (ε * ρk * Wk * Mk)) :
    |(p1m * p2k - p2m * p1k) * rt| ≤ (1 + CE ^ 2) * (K ^ 2 * Cr) * (ε * ρk * Mk ^ 2) * (Wm * Mm) := by
  have hk1 : Wk⁻¹ * Wk = 1 := inv_mul_cancel₀ hWk.ne'
  have hm1 : Wm⁻¹ * Wm = 1 := inv_mul_cancel₀ hWm.ne'
  have hWkpos : 0 ≤ Wk⁻¹ := (inv_pos.mpr hWk).le
  have hWmpos : 0 ≤ Wm⁻¹ := (inv_pos.mpr hWm).le
  have hX : |p1m * p2k - p2m * p1k| ≤ K ^ 2 * Mm * Mk * (Wm * Wk⁻¹ + Wm⁻¹ * Wk) := by
    calc |p1m * p2k - p2m * p1k| ≤ |p1m * p2k| + |p2m * p1k| := abs_sub _ _
      _ = |p1m| * |p2k| + |p2m| * |p1k| := by rw [abs_mul, abs_mul]
      _ ≤ (K * Wm * Mm) * (K * Wk⁻¹ * Mk) + (K * Wm⁻¹ * Mm) * (K * Wk * Mk) := by
          apply add_le_add
          · exact mul_le_mul h1m h2k (abs_nonneg _) (by positivity)
          · exact mul_le_mul h2m h1k (abs_nonneg _) (by positivity)
      _ = K ^ 2 * Mm * Mk * (Wm * Wk⁻¹ + Wm⁻¹ * Wk) := by ring
  have hQ : (Wm * Wk⁻¹ + Wm⁻¹ * Wk) * Wk ≤ (1 + CE ^ 2) * Wm := by
    have e1 : (Wm * Wk⁻¹ + Wm⁻¹ * Wk) * Wk = Wm + Wm⁻¹ * Wk ^ 2 := by
      have : Wm * Wk⁻¹ * Wk = Wm := by
        field_simp
      rw [add_mul, this]; ring
    have hk2 : Wk ^ 2 ≤ CE ^ 2 * Wm ^ 2 := by
      have := mul_le_mul hkm hkm hWk.le (by positivity)
      nlinarith
    have e2 : Wm⁻¹ * (CE ^ 2 * Wm ^ 2) = CE ^ 2 * Wm := by
      field_simp
    have h3 : Wm⁻¹ * Wk ^ 2 ≤ Wm⁻¹ * (CE ^ 2 * Wm ^ 2) := mul_le_mul_of_nonneg_left hk2 hWmpos
    rw [e1]
    nlinarith
  have hQ0 : 0 ≤ Wm * Wk⁻¹ + Wm⁻¹ * Wk := by positivity
  calc |(p1m * p2k - p2m * p1k) * rt| = |p1m * p2k - p2m * p1k| * |rt| := abs_mul _ _
    _ ≤ (K ^ 2 * Mm * Mk * (Wm * Wk⁻¹ + Wm⁻¹ * Wk)) * (Cr * (ε * ρk * Wk * Mk)) :=
        mul_le_mul hX hrt (abs_nonneg _) (by positivity)
    _ = (K ^ 2 * Cr * (ε * ρk * Mk ^ 2)) * (Mm) * ((Wm * Wk⁻¹ + Wm⁻¹ * Wk) * Wk) := by ring
    _ ≤ (K ^ 2 * Cr * (ε * ρk * Mk ^ 2)) * (Mm) * ((1 + CE ^ 2) * Wm) := by
        apply mul_le_mul_of_nonneg_left hQ
        positivity
    _ = (1 + CE ^ 2) * (K ^ 2 * Cr) * (ε * ρk * Mk ^ 2) * (Wm * Mm) := by ring

/-- Summand bound, the `e`-term: `|(φ¹_m r²_k - φ²_m r¹_k) e_k| ≤ (1+C_E²) K B ε ρ_k M_k² W_m M_m`. -/
theorem summand_B (CE K B ε ρk Wm Mm Wk Mk p1m p2m r1 r2 e : ℝ)
    (hCE : 0 ≤ CE) (hK : 0 ≤ K) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hρ : 0 ≤ ρk)
    (hWm : 0 < Wm) (hWk : 0 < Wk) (hMm : 0 ≤ Mm) (hMk : 0 ≤ Mk) (hkm : Wk ≤ CE * Wm)
    (h1m : |p1m| ≤ K * Wm * Mm) (h2m : |p2m| ≤ K * Wm⁻¹ * Mm)
    (hr1 : |r1| ≤ ε * ρk * Wk * Mk) (hr2 : |r2| ≤ ε * ρk * Wk⁻¹ * Mk)
    (he : |e| ≤ B * (Wk * Mk)) :
    |(p1m * r2 - p2m * r1) * e| ≤ (1 + CE ^ 2) * (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) := by
  have hk1 : Wk * Wk⁻¹ = 1 := mul_inv_cancel₀ hWk.ne'
  have hm1 : Wm⁻¹ * Wm = 1 := inv_mul_cancel₀ hWm.ne'
  have hWmpos : 0 ≤ Wm⁻¹ := (inv_pos.mpr hWm).le
  have hk2 : Wk ^ 2 ≤ CE ^ 2 * Wm ^ 2 := by
    have := mul_le_mul hkm hkm hWk.le (by positivity)
    nlinarith
  have hA : |p1m * r2| * |e| ≤ (K * Wm * Mm) * (ε * ρk * Wk⁻¹ * Mk) * (B * (Wk * Mk)) := by
    calc |p1m * r2| * |e| = |p1m| * |r2| * |e| := by rw [abs_mul]
      _ ≤ (K * Wm * Mm) * (ε * ρk * Wk⁻¹ * Mk) * (B * (Wk * Mk)) := by
          apply mul_le_mul (mul_le_mul h1m hr2 (abs_nonneg _) (by positivity)) he (abs_nonneg _) (by positivity)
  have hB' : |p2m * r1| * |e| ≤ (K * Wm⁻¹ * Mm) * (ε * ρk * Wk * Mk) * (B * (Wk * Mk)) := by
    calc |p2m * r1| * |e| = |p2m| * |r1| * |e| := by rw [abs_mul]
      _ ≤ (K * Wm⁻¹ * Mm) * (ε * ρk * Wk * Mk) * (B * (Wk * Mk)) := by
          apply mul_le_mul (mul_le_mul h2m hr1 (abs_nonneg _) (by positivity)) he (abs_nonneg _) (by positivity)
  have hfin1 : (K * Wm * Mm) * (ε * ρk * Wk⁻¹ * Mk) * (B * (Wk * Mk))
      = (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) := by
    have : (K * Wm * Mm) * (ε * ρk * Wk⁻¹ * Mk) * (B * (Wk * Mk))
        = (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) * (Wk * Wk⁻¹) := by ring
    rw [this, hk1, mul_one]
  have hfin2 : (K * Wm⁻¹ * Mm) * (ε * ρk * Wk * Mk) * (B * (Wk * Mk))
      ≤ (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) * CE ^ 2 := by
    have : (K * Wm⁻¹ * Mm) * (ε * ρk * Wk * Mk) * (B * (Wk * Mk))
        = (K * B) * (ε * ρk * Mk ^ 2) * Mm * (Wk ^ 2 * Wm⁻¹) := by ring
    rw [this]
    have h5 : Wk ^ 2 * Wm⁻¹ ≤ CE ^ 2 * Wm := by
      have := mul_le_mul_of_nonneg_right hk2 hWmpos
      have e2 : CE ^ 2 * Wm ^ 2 * Wm⁻¹ = CE ^ 2 * Wm := by
        field_simp
      linarith
    have hc : 0 ≤ (K * B) * (ε * ρk * Mk ^ 2) * Mm := by positivity
    calc (K * B) * (ε * ρk * Mk ^ 2) * Mm * (Wk ^ 2 * Wm⁻¹)
        ≤ (K * B) * (ε * ρk * Mk ^ 2) * Mm * (CE ^ 2 * Wm) := mul_le_mul_of_nonneg_left h5 hc
      _ = (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) * CE ^ 2 := by ring
  calc |(p1m * r2 - p2m * r1) * e| = |p1m * r2 - p2m * r1| * |e| := abs_mul _ _
    _ ≤ (|p1m * r2| + |p2m * r1|) * |e| := by
        apply mul_le_mul_of_nonneg_right (abs_sub _ _) (abs_nonneg _)
    _ = |p1m * r2| * |e| + |p2m * r1| * |e| := by ring
    _ ≤ (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) + (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) * CE ^ 2 := by
        apply add_le_add
        · rw [hfin1] at hA; exact hA
        · exact le_trans hB' hfin2
    _ = (1 + CE ^ 2) * (K * B) * (ε * ρk * Mk ^ 2) * (Wm * Mm) := by ring

/-- Base site of a patch with entry flux: the Cramer identity at the entry bond `s - 1` gives the bound at `s`. -/
theorem base_site (ω cm CE K a V : ℝ) (A : ℤ → ℝ) (s : ℤ) (e φ1 φ2 W M : ℤ → ℝ)
    (hω : 0 < ω) (hcm : 0 < cm) (hCE : 0 ≤ CE) (hK : 0 ≤ K) (ha : 0 ≤ a) (hV0 : 0 ≤ V)
    (hWs : 0 < W s) (hMs : 0 ≤ M s)
    (hS1 : cm * ω ≤ |cas A φ1 φ2 (s - 1)|)
    (hφ1 : |φ1 s| ≤ K * W s * M s) (hφ2 : |φ2 s| ≤ K * (W s)⁻¹ * M s)
    (hV : V ≤ CE * W s)
    (hF2 : |cas A e φ2 (s - 1)| ≤ a * ω) (hF1 : |cas A e φ1 (s - 1)| ≤ a * ω * V ^ 2) :
    |e s| ≤ (1 + CE ^ 2) / cm * K * a * (W s * M s) := by
  have hC := cramer_first e φ1 φ2 A (s - 1)
  rw [sub_add_cancel] at hC
  have hkey : e s * cas A φ1 φ2 (s - 1) = φ1 s * cas A e φ2 (s - 1) - φ2 s * cas A e φ1 (s - 1) := by
    linarith [hC]
  have habs : |e s| * |cas A φ1 φ2 (s - 1)| = |φ1 s * cas A e φ2 (s - 1) - φ2 s * cas A e φ1 (s - 1)| := by
    rw [← abs_mul, hkey]
  have hV2 : V ^ 2 ≤ CE ^ 2 * W s ^ 2 := by
    have := mul_le_mul hV hV hV0 (by positivity)
    nlinarith
  have hWinv : 0 ≤ (W s)⁻¹ := (inv_pos.mpr hWs).le
  have hWW : (W s)⁻¹ * W s = 1 := inv_mul_cancel₀ hWs.ne'
  have t1 : |φ1 s| * |cas A e φ2 (s - 1)| ≤ (K * W s * M s) * (a * ω) :=
    mul_le_mul hφ1 hF2 (abs_nonneg _) (by positivity)
  have t2 : |φ2 s| * |cas A e φ1 (s - 1)| ≤ (K * (W s)⁻¹ * M s) * (a * ω * (CE ^ 2 * W s ^ 2)) := by
    apply mul_le_mul hφ2 (le_trans hF1 (mul_le_mul_of_nonneg_left hV2 (by positivity)))
      (abs_nonneg _) (by positivity)
  have t3 : (K * (W s)⁻¹ * M s) * (a * ω * (CE ^ 2 * W s ^ 2)) = (K * CE ^ 2 * a * ω) * (W s * M s) := by
    have : (K * (W s)⁻¹ * M s) * (a * ω * (CE ^ 2 * W s ^ 2))
        = (K * CE ^ 2 * a * ω) * (W s * M s) * ((W s)⁻¹ * W s) := by ring
    rw [this, hWW, mul_one]
  have hup : |e s| * (cm * ω) ≤ (K * (1 + CE ^ 2) * a * ω) * (W s * M s) := by
    have h1 : |e s| * (cm * ω) ≤ |e s| * |cas A φ1 φ2 (s - 1)| :=
      mul_le_mul_of_nonneg_left hS1 (abs_nonneg _)
    have h2 := abs_sub (φ1 s * cas A e φ2 (s - 1)) (φ2 s * cas A e φ1 (s - 1))
    rw [abs_mul, abs_mul] at h2
    have h4 : |φ1 s| * |cas A e φ2 (s - 1)| + |φ2 s| * |cas A e φ1 (s - 1)|
        ≤ (K * W s * M s) * (a * ω) + (K * CE ^ 2 * a * ω) * (W s * M s) := by
      rw [← t3]; linarith [t1, t2]
    have h5 : (K * W s * M s) * (a * ω) + (K * CE ^ 2 * a * ω) * (W s * M s)
        = (K * (1 + CE ^ 2) * a * ω) * (W s * M s) := by ring
    linarith [h1, habs, h2, h4, h5]
  have hcmω : 0 < cm * ω := mul_pos hcm hω
  have hfin : |e s| * (cm * ω) ≤ ((1 + CE ^ 2) / cm * K * a * (W s * M s)) * (cm * ω) := by
    have : ((1 + CE ^ 2) / cm * K * a * (W s * M s)) * (cm * ω) = (K * (1 + CE ^ 2) * a * ω) * (W s * M s) := by
      field_simp
    rw [this]; exact hup
  exact le_of_mul_le_mul_right hfin hcmω

/-- The summand of the Volterra sum (`eq:eng-volterra` of the appendix), with `r^α_k = Lh φ^α_k`:
`(φ¹_m φ²_k - φ²_m φ¹_k) rt_k + (φ¹_m r²_k - φ²_m r¹_k) e_k`. -/
noncomputable def volT (h : ℝ) (A Q : ℤ → ℝ) (φ1 φ2 e rt : ℤ → ℝ) (m k : ℤ) : ℝ :=
  (φ1 m * φ2 k - φ2 m * φ1 k) * rt k + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k

lemma sq_le_of_le_nonneg {x y C : ℝ} (hx : 0 ≤ x) (hxy : x ≤ C * y) (hC : 0 ≤ C) (hy : 0 ≤ y) :
    x ^ 2 ≤ C ^ 2 * y ^ 2 := by
  have h1 : x * x ≤ (C * y) * (C * y) := mul_le_mul hxy hxy hx (mul_nonneg hC hy)
  calc x ^ 2 = x * x := by ring
    _ ≤ (C * y) * (C * y) := h1
    _ = C ^ 2 * y ^ 2 := by ring

/-- **One patch** (`app:eng-twopatch`, the induction on the sites of a patch with an entry flux).  The patch has
equation sites `s, …, b`, sites `s-1, …, b+1`, entry bond `s-1` with fluxes `F^α = 𝒲_{s-1}(e, φ^α)` bounded by
`a ω` (`α = 2`) and `a ω V²` (`α = 1`), and exit bond `b`.  Conclusions: the Volterra bound
`|e_m| ≤ B W_m M_m` on `s, …, b+1` with `B = 2 D K (a + K C_r θ)`, `D = (1+C_E²)/c₋`, `θ = ε h S/ω`,
`S = ∑_{k∈[s,b]} ρ_k M_k²`, and the exit fluxes `|𝒲_b(e,φ²)| ≤ 2ω(a + K C_r θ)`,
`|𝒲_b(e,φ¹)| ≤ 2 C_E² W_b² ω(a + K C_r θ)`. -/
theorem patch_step (h ω cm CE K ε Cr a V S θ Bq : ℝ) (A Q : ℤ → ℝ) (s b : ℤ)
    (e φ1 φ2 rt ρ M W : ℤ → ℝ)
    (hh : 0 < h) (hω : 0 < ω) (hcm : 0 < cm) (hCE : 0 ≤ CE) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hCr : 0 ≤ Cr) (ha : 0 ≤ a) (hV0 : 0 ≤ V) (hBq0 : 0 ≤ Bq)
    (hS : S = ∑ k ∈ Icc s b, ρ k * M k ^ 2) (hθ0 : 0 ≤ θ) (hθω : θ * ω = ε * (h * S))
    (hDKa : (1 + CE ^ 2) / cm * K * a ≤ Bq)
    (hGb : a + (K * Cr + Bq) * θ ≤ 2 * (a + K * Cr * θ))
    (hcBq : cm * Bq = 2 * (1 + CE ^ 2) * K * (a + K * Cr * θ))
    (hS1 : ∀ j ∈ Icc s b, cm * ω ≤ |cas A φ1 φ2 j|)
    (hMpos : ∀ j ∈ Icc s (b + 1), 0 < M j) (hWpos : ∀ j ∈ Icc s (b + 1), 0 < W j)
    (hmono : ∀ k ∈ Icc s (b + 1), ∀ j ∈ Icc s (b + 1), k ≤ j → W k ≤ CE * W j)
    (hφ1 : ∀ j ∈ Icc s (b + 1), |φ1 j| ≤ K * W j * M j)
    (hφ2 : ∀ j ∈ Icc s (b + 1), |φ2 j| ≤ K * (W j)⁻¹ * M j)
    (hρ : ∀ k, 0 ≤ ρ k)
    (hr1 : ∀ k ∈ Icc s b, |Lh h A Q φ1 k| ≤ ε * ρ k * W k * M k)
    (hr2 : ∀ k ∈ Icc s b, k ≠ 0 → |Lh h A Q φ2 k| ≤ ε * ρ k * (W k)⁻¹ * M k)
    (hLe : ∀ k ∈ Icc s b, Lop A Q e k = -(h * rt k))
    (hrt : ∀ k ∈ Icc s b, |rt k| ≤ Cr * (ε * ρ k * W k * M k))
    (he0 : ∀ k ∈ Icc s b, k = 0 → e k = 0)
    (hV : ∀ m ∈ Icc s (b + 1), V ≤ CE * W m)
    (hF2 : |cas A e φ2 (s - 1)| ≤ a * ω)
    (hF1 : |cas A e φ1 (s - 1)| ≤ a * ω * V ^ 2)
    (m : ℤ) (hm : m ∈ Icc (s + 1) (b + 1))
    (IH : ∀ k ∈ Icc s (m - 1), |e k| ≤ Bq * (W k * M k)) :
    |e m| ≤ Bq * (W m * M m) := by
  have hmI : m ∈ Icc s (b + 1) := mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩
  have hLe' : ∀ k ∈ Icc s (m - 1), Lop A Q e k = -(h * rt k) := by
    intro k hk
    have hk' := mem_Icc.mp hk
    exact hLe k (mem_Icc.mpr ⟨hk'.1, by have := (mem_Icc.mp hmI).2; omega⟩)
  have hC := cramer_first e φ1 φ2 A (m - 1)
  rw [sub_add_cancel] at hC
  have hF2e := flux_telescope h hh.ne' A Q e φ2 rt s m (by have := (mem_Icc.mp hm).1; omega) hLe'
  have hF1e := flux_telescope h hh.ne' A Q e φ1 rt s m (by have := (mem_Icc.mp hm).1; omega) hLe'
  have hWm := hWpos m hmI
  have hMm := hMpos m hmI
  have hsplit : φ1 m * (∑ k ∈ Icc s (m - 1), (φ2 k * rt k + e k * Lh h A Q φ2 k))
      - φ2 m * (∑ k ∈ Icc s (m - 1), (φ1 k * rt k + e k * Lh h A Q φ1 k))
      = ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    unfold volT
    ring
  have hkey : e m * cas A φ1 φ2 (m - 1)
      = φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)
        - h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k := by
    rw [hF2e, hF1e] at hC
    linear_combination (-1 : ℝ) * hC - h * hsplit
  -- bound on each summand
  have hTk : ∀ k ∈ Icc s (m - 1), |volT h A Q φ1 φ2 e rt m k|
      ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m) := by
    intro k hk
    have hk' := mem_Icc.mp hk
    have hkb : k ∈ Icc s b := mem_Icc.mpr ⟨hk'.1, by have := (mem_Icc.mp hmI).2; omega⟩
    have hkm : k ∈ Icc s (b + 1) := mem_Icc.mpr ⟨hk'.1, by have := (mem_Icc.mp hkb).2; omega⟩
    have hWk := hWpos k hkm
    have hMk := hMpos k hkm
    have hρk := hρ k
    have hkmW : W k ≤ CE * W m := hmono k hkm m hmI (by omega)
    have hA := summand_A CE K Cr ε (ρ k) (W m) (M m) (W k) (M k) (φ1 m) (φ2 m) (φ1 k) (φ2 k) (rt k)
      hCE hK hCr hε hρk hWm hWk hMm.le hMk.le hkmW (hφ1 m hmI) (hφ2 m hmI) (hφ1 k hkm)
      (hφ2 k hkm) (hrt k hkb)
    have hX : 0 ≤ (ε * ρ k * M k ^ 2) * (W m * M m) :=
      mul_nonneg (mul_nonneg hε hρk) (sq_nonneg _) |>.trans_eq rfl |> fun h' => mul_nonneg h' (mul_nonneg hWm.le hMm.le)
    have hAcoef : (1 + CE ^ 2) * (K ^ 2 * Cr) * (ε * ρ k * M k ^ 2) * (W m * M m)
        ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m) := by
      have hc : (1 + CE ^ 2) * (K ^ 2 * Cr) ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) :=
        mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hK hBq0]) (by positivity)
      calc (1 + CE ^ 2) * (K ^ 2 * Cr) * (ε * ρ k * M k ^ 2) * (W m * M m)
          = ((1 + CE ^ 2) * (K ^ 2 * Cr)) * ((ε * ρ k * M k ^ 2) * (W m * M m)) := by ring
        _ ≤ ((1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq)) * ((ε * ρ k * M k ^ 2) * (W m * M m)) :=
            mul_le_mul_of_nonneg_right hc hX
        _ = (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m) := by ring
    by_cases hk0 : k = 0
    · have hek : e k = 0 := he0 k hkb hk0
      have hVeq : volT h A Q φ1 φ2 e rt m k = (φ1 m * φ2 k - φ2 m * φ1 k) * rt k := by
        unfold volT
        rw [hek]
        ring
      rw [hVeq]
      exact le_trans hA hAcoef
    · have hB' := summand_B CE K Bq ε (ρ k) (W m) (M m) (W k) (M k) (φ1 m) (φ2 m) (Lh h A Q φ1 k)
        (Lh h A Q φ2 k) (e k) hCE hK hBq0 hε hρk hWm hWk hMm.le hMk.le hkmW (hφ1 m hmI) (hφ2 m hmI)
        (hr1 k hkb) (hr2 k hkb hk0) (IH k (mem_Icc.mpr ⟨hk'.1, by omega⟩))
      have hVsplit : volT h A Q φ1 φ2 e rt m k
          = (φ1 m * φ2 k - φ2 m * φ1 k) * rt k
            + (φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k := rfl
      have hTsplit : |volT h A Q φ1 φ2 e rt m k| ≤ |(φ1 m * φ2 k - φ2 m * φ1 k) * rt k|
          + |(φ1 m * Lh h A Q φ2 k - φ2 m * Lh h A Q φ1 k) * e k| := by
        rw [hVsplit]; exact abs_add_le _ _
      have hBcoef : (1 + CE ^ 2) * (K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m)
          + (1 + CE ^ 2) * (K ^ 2 * Cr) * (ε * ρ k * M k ^ 2) * (W m * M m)
          = (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m) := by ring
      have hBle := hB'
      linarith [hA, hBle, hTsplit, hBcoef]
  -- sum of the summands
  have hsumT : |∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
      ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (ε * S) := by
    have hεS : ε * S = ∑ k ∈ Icc s b, ε * (ρ k * M k ^ 2) := by
      rw [hS, Finset.mul_sum]
    have hK2 : 0 ≤ K ^ 2 * Cr + K * Bq := add_nonneg (mul_nonneg (sq_nonneg K) hCr) (mul_nonneg hK hBq0)
    have hnn : 0 ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) :=
      mul_nonneg (mul_nonneg (by positivity) hK2) (mul_nonneg hWm.le hMm.le)
    have hsub : ∑ k ∈ Icc s (m - 1), ε * (ρ k * M k ^ 2) ≤ ∑ k ∈ Icc s b, ε * (ρ k * M k ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc le_rfl (by have := (mem_Icc.mp hmI).2; omega)
      · intro k _ _
        exact mul_nonneg hε (mul_nonneg (hρ k) (sq_nonneg _))
    calc |∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
        ≤ ∑ k ∈ Icc s (m - 1), |volT h A Q φ1 φ2 e rt m k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc s (m - 1), (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (ε * ρ k * M k ^ 2) * (W m * M m) :=
          Finset.sum_le_sum hTk
      _ = (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m)
            * (∑ k ∈ Icc s (m - 1), ε * (ρ k * M k ^ 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (ε * S) := by
          rw [hεS]
          exact mul_le_mul_of_nonneg_left hsub hnn
  -- the main estimate
  have hcas := hS1 (m - 1) (mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, by have := (mem_Icc.mp hm).2; omega⟩)
  have hcmω : 0 < cm * ω := mul_pos hcm hω
  have habs : |e m| * (cm * ω) ≤ |e m| * |cas A φ1 φ2 (m - 1)| :=
    mul_le_mul_of_nonneg_left hcas (abs_nonneg _)
  have habs2 : |e m| * |cas A φ1 φ2 (m - 1)|
      = |φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)
          - h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k| := by
    rw [← abs_mul, hkey]
  have hR := abs_sub (φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1))
    (h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k)
  have hR2 := abs_sub (φ1 m * cas A e φ2 (s - 1)) (φ2 m * cas A e φ1 (s - 1))
  rw [abs_mul, abs_mul] at hR2
  have habsT : |h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
      = h * |∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k| := by
    rw [abs_mul, abs_of_pos hh]
  have hWW : (W m)⁻¹ * W m = 1 := inv_mul_cancel₀ hWm.ne'
  have hV2 : V ^ 2 ≤ CE ^ 2 * W m ^ 2 := sq_le_of_le_nonneg hV0 (hV m hmI) hCE hWm.le
  have hF1' : |cas A e φ1 (s - 1)| ≤ a * ω * (CE ^ 2 * W m ^ 2) :=
    le_trans hF1 (mul_le_mul_of_nonneg_left hV2 (mul_nonneg ha hω.le))
  have u1 : |φ1 m| * |cas A e φ2 (s - 1)| ≤ (K * W m * M m) * (a * ω) :=
    mul_le_mul (hφ1 m hmI) hF2 (abs_nonneg _) (mul_nonneg (mul_nonneg hK hWm.le) hMm.le)
  have u2 : |φ2 m| * |cas A e φ1 (s - 1)| ≤ (K * (W m)⁻¹ * M m) * (a * ω * (CE ^ 2 * W m ^ 2)) :=
    mul_le_mul (hφ2 m hmI) hF1' (abs_nonneg _)
      (mul_nonneg (mul_nonneg hK (inv_nonneg.mpr hWm.le)) hMm.le)
  have u3 : (K * (W m)⁻¹ * M m) * (a * ω * (CE ^ 2 * W m ^ 2)) = (K * CE ^ 2 * a * ω) * (W m * M m) := by
    have : (K * (W m)⁻¹ * M m) * (a * ω * (CE ^ 2 * W m ^ 2))
        = (K * CE ^ 2 * a * ω) * (W m * M m) * ((W m)⁻¹ * W m) := by ring
    rw [this, hWW, mul_one]
  have u4 : h * |∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
      ≤ h * ((1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (ε * S)) :=
    mul_le_mul_of_nonneg_left hsumT hh.le
  have u5 : h * ((1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (ε * S))
      = (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (θ * ω) := by
    rw [hθω]; ring
  have hRR : |φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)
        - h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
      ≤ (K * (1 + CE ^ 2) * a * ω) * (W m * M m)
        + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (θ * ω) := by
    have hh6 : (K * W m * M m) * (a * ω) + (K * CE ^ 2 * a * ω) * (W m * M m)
        = (K * (1 + CE ^ 2) * a * ω) * (W m * M m) := by ring
    have hpart : |φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)|
        ≤ (K * (1 + CE ^ 2) * a * ω) * (W m * M m) := by
      linarith [hR2, u1, u2, u3, hh6]
    have hfin : |φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)
        - h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k|
        ≤ |φ1 m * cas A e φ2 (s - 1) - φ2 m * cas A e φ1 (s - 1)|
          + |h * ∑ k ∈ Icc s (m - 1), volT h A Q φ1 φ2 e rt m k| := hR
    linarith [hfin, hpart, habsT, u4, u5]
  have hQ : |e m| * (cm * ω) ≤ ((K * (1 + CE ^ 2) * a + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * θ)
      * (W m * M m)) * ω := by
    have h7 : (K * (1 + CE ^ 2) * a * ω) * (W m * M m)
        + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * (W m * M m) * (θ * ω)
        = ((K * (1 + CE ^ 2) * a + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * θ) * (W m * M m)) * ω := by ring
    linarith [habs, habs2, hRR, h7]
  have hQle : (K * (1 + CE ^ 2) * a + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * θ) ≤ cm * Bq := by
    have e1 : K * (1 + CE ^ 2) * a + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * θ
        = (1 + CE ^ 2) * K * (a + (K * Cr + Bq) * θ) := by ring
    rw [e1, hcBq]
    have hc : 0 ≤ (1 + CE ^ 2) * K := mul_nonneg (by positivity) hK
    have := mul_le_mul_of_nonneg_left hGb hc
    linarith [this]
  have hWMpos : 0 ≤ W m * M m := mul_nonneg hWm.le hMm.le
  have hfin : |e m| * (cm * ω) ≤ (Bq * (W m * M m)) * (cm * ω) := by
    have hmid : ((K * (1 + CE ^ 2) * a + (1 + CE ^ 2) * (K ^ 2 * Cr + K * Bq) * θ) * (W m * M m)) * ω
        ≤ (cm * Bq) * (W m * M m) * ω :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQle hWMpos) hω.le
    have e2 : (Bq * (W m * M m)) * (cm * ω) = (cm * Bq) * (W m * M m) * ω := by ring
    rw [e2]
    linarith [hQ, hmid]
  exact le_of_mul_le_mul_right hfin hcmω

/-- **One patch, all sites** (`app:eng-twopatch`).  Under the entry-flux hypotheses, the Volterra bound
`|e_m| ≤ B W_m M_m` holds on the sites `s, …, b+1`, and the exit fluxes on the bond `b` are bounded. -/
theorem patch_volterra (h ω cm CE K ε Cr a V S θ Bq : ℝ) (A Q : ℤ → ℝ) (s b : ℤ)
    (e φ1 φ2 rt ρ M W : ℤ → ℝ)
    (hh : 0 < h) (hω : 0 < ω) (hcm : 0 < cm) (hCE : 0 ≤ CE) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hCr : 0 ≤ Cr) (ha : 0 ≤ a) (hV0 : 0 ≤ V) (hsb : s ≤ b)
    (hS : S = ∑ k ∈ Icc s b, ρ k * M k ^ 2) (hθ0 : 0 ≤ θ) (hθω : θ * ω = ε * (h * S))
    (hsmall : 2 * ((1 + CE ^ 2) / cm) * K * θ ≤ 1)
    (hB : Bq = 2 * ((1 + CE ^ 2) / cm) * K * (a + K * Cr * θ))
    (hS1 : ∀ j ∈ Icc s b, cm * ω ≤ |cas A φ1 φ2 j|)
    (hMpos : ∀ j ∈ Icc s (b + 1), 0 < M j) (hWpos : ∀ j ∈ Icc s (b + 1), 0 < W j)
    (hmono : ∀ k ∈ Icc s (b + 1), ∀ j ∈ Icc s (b + 1), k ≤ j → W k ≤ CE * W j)
    (hφ1 : ∀ j ∈ Icc s (b + 1), |φ1 j| ≤ K * W j * M j)
    (hφ2 : ∀ j ∈ Icc s (b + 1), |φ2 j| ≤ K * (W j)⁻¹ * M j)
    (hρ : ∀ k, 0 ≤ ρ k)
    (hr1 : ∀ k ∈ Icc s b, |Lh h A Q φ1 k| ≤ ε * ρ k * W k * M k)
    (hr2 : ∀ k ∈ Icc s b, k ≠ 0 → |Lh h A Q φ2 k| ≤ ε * ρ k * (W k)⁻¹ * M k)
    (hLe : ∀ k ∈ Icc s b, Lop A Q e k = -(h * rt k))
    (hrt : ∀ k ∈ Icc s b, |rt k| ≤ Cr * (ε * ρ k * W k * M k))
    (he0 : ∀ k ∈ Icc s b, k = 0 → e k = 0)
    (hV : ∀ m ∈ Icc s (b + 1), V ≤ CE * W m)
    (hF2 : |cas A e φ2 (s - 1)| ≤ a * ω)
    (hF1 : |cas A e φ1 (s - 1)| ≤ a * ω * V ^ 2)
    (hbase : |e s| ≤ (1 + CE ^ 2) / cm * K * a * (W s * M s)) :
    (∀ m ∈ Icc s (b + 1), |e m| ≤ Bq * (W m * M m)) ∧
    |cas A e φ2 b| ≤ 2 * ω * (a + K * Cr * θ) ∧
    |cas A e φ1 b| ≤ 2 * CE ^ 2 * (W b) ^ 2 * (ω * (a + K * Cr * θ)) := by
  have hD0 : 0 ≤ (1 + CE ^ 2) / cm := by positivity
  have hG0 : 0 ≤ a + K * Cr * θ := by
    have := mul_nonneg (mul_nonneg hK hCr) hθ0
    linarith
  have hBq0 : 0 ≤ Bq := by
    rw [hB]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD0) hK) hG0
  have hBθ : Bq * θ ≤ a + K * Cr * θ := by
    calc Bq * θ = (2 * ((1 + CE ^ 2) / cm) * K * θ) * (a + K * Cr * θ) := by rw [hB]; ring
      _ ≤ 1 * (a + K * Cr * θ) := mul_le_mul_of_nonneg_right hsmall hG0
      _ = a + K * Cr * θ := one_mul _
  have hGb : a + (K * Cr + Bq) * θ ≤ 2 * (a + K * Cr * θ) := by
    have : a + (K * Cr + Bq) * θ = (a + K * Cr * θ) + Bq * θ := by ring
    rw [this]; linarith
  have hDKa : (1 + CE ^ 2) / cm * K * a ≤ Bq := by
    rw [hB]
    have ht : 0 ≤ (1 + CE ^ 2) / cm * K := mul_nonneg hD0 hK
    nlinarith [mul_nonneg ht (mul_nonneg hK (mul_nonneg hCr hθ0))]
  have hcBq : cm * Bq = 2 * (1 + CE ^ 2) * K * (a + K * Cr * θ) := by
    rw [hB]; field_simp
  -- induction over the sites
  have hall : ∀ n : ℕ, ∀ k : ℤ, s ≤ k → k ≤ s + n → k ≤ b + 1 → |e k| ≤ Bq * (W k * M k) := by
    intro n
    induction n with
    | zero =>
      intro k hk1 hk2 hk3
      have hks : k = s := by push_cast at hk2; omega
      subst hks
      exact le_trans hbase (mul_le_mul_of_nonneg_right hDKa
        (mul_nonneg (hWpos k (mem_Icc.mpr ⟨le_rfl, by omega⟩)).le (hMpos k (mem_Icc.mpr ⟨le_rfl, by omega⟩)).le))
    | succ n ih =>
      intro k hk1 hk2 hk3
      by_cases hkn : k ≤ s + n
      · exact ih k hk1 hkn hk3
      · have hkm : k ∈ Icc (s + 1) (b + 1) := mem_Icc.mpr ⟨by push_cast at hk2; omega, hk3⟩
        exact patch_step h ω cm CE K ε Cr a V S θ Bq A Q s b e φ1 φ2 rt ρ M W hh hω hcm hCE hK hε hCr ha
          hV0 hBq0 hS hθ0 hθω hDKa hGb hcBq hS1 hMpos hWpos hmono hφ1 hφ2 hρ hr1 hr2 hLe hrt he0 hV hF2 hF1
          k hkm (fun j hj => by
            have hj' := mem_Icc.mp hj
            exact ih j hj'.1 (by push_cast at hk2; omega) (by omega))
  have hbound : ∀ m ∈ Icc s (b + 1), |e m| ≤ Bq * (W m * M m) := by
    intro m hm
    have hm' := mem_Icc.mp hm
    exact hall (m - s).toNat m hm'.1 (by rw [Int.toNat_of_nonneg (by omega)]; omega) hm'.2
  -- the exit fluxes on the bond b
  have hb1 : b + 1 - 1 = b := by ring
  have hLeb : ∀ k ∈ Icc s (b + 1 - 1), Lop A Q e k = -(h * rt k) := fun k hk => hLe k (by rw [hb1] at hk; exact hk)
  have hX2 := flux_telescope h hh.ne' A Q e φ2 rt s (b + 1) (by omega) hLeb
  have hX1 := flux_telescope h hh.ne' A Q e φ1 rt s (b + 1) (by omega) hLeb
  rw [hb1] at hX2 hX1
  have hεS' : ∀ c : ℝ, c * (ε * S) = ∑ k ∈ Icc s b, c * (ε * ρ k * M k ^ 2) := by
    intro c
    rw [hS, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hW2b : ∀ k ∈ Icc s b, W k ^ 2 ≤ CE ^ 2 * W b ^ 2 := fun k hk =>
    sq_le_of_le_nonneg (hWpos k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩)).le
      (hmono k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, by have := (mem_Icc.mp hk).2; omega⟩) b
        (mem_Icc.mpr ⟨hsb, by omega⟩) (mem_Icc.mp hk).2) hCE (hWpos b (mem_Icc.mpr ⟨hsb, by omega⟩)).le
  -- the term bound for the φ² flux
  have htermB : ∀ k ∈ Icc s b, |φ2 k * rt k + e k * Lh h A Q φ2 k| ≤ (K * Cr + Bq) * (ε * ρ k * M k ^ 2) := by
    intro k hk
    have hkb := mem_Icc.mp hk
    have hkm : k ∈ Icc s (b + 1) := mem_Icc.mpr ⟨hkb.1, by omega⟩
    have hWk := hWpos k hkm
    have hMk := hMpos k hkm
    have hρk := hρ k
    have hWW : (W k)⁻¹ * W k = 1 := inv_mul_cancel₀ hWk.ne'
    have t1 : |φ2 k * rt k| ≤ K * Cr * (ε * ρ k * M k ^ 2) := by
      rw [abs_mul]
      have := mul_le_mul (hφ2 k hkm) (hrt k hk) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hK (inv_nonneg.mpr hWk.le)) hMk.le)
      calc |φ2 k| * |rt k| ≤ (K * (W k)⁻¹ * M k) * (Cr * (ε * ρ k * W k * M k)) := this
        _ = K * Cr * (ε * ρ k * M k ^ 2) * ((W k)⁻¹ * W k) := by ring
        _ = K * Cr * (ε * ρ k * M k ^ 2) := by rw [hWW, mul_one]
    have t2 : |e k * Lh h A Q φ2 k| ≤ Bq * (ε * ρ k * M k ^ 2) := by
      by_cases hk0 : k = 0
      · rw [he0 k hk hk0, zero_mul, abs_zero]
        exact mul_nonneg hBq0 (mul_nonneg (mul_nonneg hε hρk) (sq_nonneg _))
      · rw [abs_mul]
        have := mul_le_mul (hbound k hkm) (hr2 k hk hk0) (abs_nonneg _)
          (mul_nonneg hBq0 (mul_nonneg hWk.le hMk.le))
        calc |e k| * |Lh h A Q φ2 k| ≤ (Bq * (W k * M k)) * (ε * ρ k * (W k)⁻¹ * M k) := this
          _ = Bq * (ε * ρ k * M k ^ 2) * ((W k)⁻¹ * W k) := by ring
          _ = Bq * (ε * ρ k * M k ^ 2) := by rw [hWW, mul_one]
    have := abs_add_le (φ2 k * rt k) (e k * Lh h A Q φ2 k)
    have e5 : (K * Cr + Bq) * (ε * ρ k * M k ^ 2) = K * Cr * (ε * ρ k * M k ^ 2) + Bq * (ε * ρ k * M k ^ 2) := by
      ring
    linarith
  have hsumB : |∑ k ∈ Icc s b, (φ2 k * rt k + e k * Lh h A Q φ2 k)| ≤ (K * Cr + Bq) * (ε * S) := by
    rw [hεS' (K * Cr + Bq)]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun k hk => htermB k hk))
  have hh2 : h * |∑ k ∈ Icc s b, (φ2 k * rt k + e k * Lh h A Q φ2 k)| ≤ (K * Cr + Bq) * (θ * ω) := by
    have := mul_le_mul_of_nonneg_left hsumB hh.le
    have e7 : h * ((K * Cr + Bq) * (ε * S)) = (K * Cr + Bq) * (θ * ω) := by
      rw [hθω]; ring
    linarith
  have hcas2 : |cas A e φ2 b| ≤ 2 * ω * (a + K * Cr * θ) := by
    rw [hX2]
    have hab := abs_sub (cas A e φ2 (s - 1)) (h * ∑ k ∈ Icc s b, (φ2 k * rt k + e k * Lh h A Q φ2 k))
    rw [abs_mul, abs_of_pos hh] at hab
    have e8 : ω * (a + (K * Cr + Bq) * θ) ≤ ω * (2 * (a + K * Cr * θ)) := mul_le_mul_of_nonneg_left hGb hω.le
    have e9 : ω * (a + (K * Cr + Bq) * θ) = a * ω + (K * Cr + Bq) * (θ * ω) := by ring
    have e10 : ω * (2 * (a + K * Cr * θ)) = 2 * ω * (a + K * Cr * θ) := by ring
    linarith [hab, hh2, hF2, e8, e9, e10]
  -- the term bound for the φ¹ flux
  have hterm1 : ∀ k ∈ Icc s b, |φ1 k * rt k + e k * Lh h A Q φ1 k|
      ≤ (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (ε * ρ k * M k ^ 2) := by
    intro k hk
    have hkb := mem_Icc.mp hk
    have hkm : k ∈ Icc s (b + 1) := mem_Icc.mpr ⟨hkb.1, by omega⟩
    have hWk := hWpos k hkm
    have hMk := hMpos k hkm
    have hρk := hρ k
    have hW2 := hW2b k hk
    have hX0 : 0 ≤ ε * ρ k * M k ^ 2 := mul_nonneg (mul_nonneg hε hρk) (sq_nonneg _)
    have t1 : |φ1 k * rt k| ≤ K * Cr * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) := by
      rw [abs_mul]
      have := mul_le_mul (hφ1 k hkm) (hrt k hk) (abs_nonneg _) (mul_nonneg (mul_nonneg hK hWk.le) hMk.le)
      have e11 : K * W k * M k * (Cr * (ε * ρ k * W k * M k)) = K * Cr * (ε * ρ k * M k ^ 2) * W k ^ 2 := by
        ring
      rw [e11] at this
      calc |φ1 k| * |rt k| ≤ K * Cr * (ε * ρ k * M k ^ 2) * W k ^ 2 := this
        _ ≤ K * Cr * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) :=
            mul_le_mul_of_nonneg_left hW2 (mul_nonneg (mul_nonneg hK hCr) hX0)
    have t2 : |e k * Lh h A Q φ1 k| ≤ Bq * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) := by
      by_cases hk0 : k = 0
      · rw [he0 k hk hk0, zero_mul, abs_zero]
        exact mul_nonneg (mul_nonneg hBq0 hX0) (mul_nonneg (sq_nonneg CE) (sq_nonneg _))
      · rw [abs_mul]
        have := mul_le_mul (hbound k hkm) (hr1 k hk) (abs_nonneg _) (mul_nonneg hBq0 (mul_nonneg hWk.le hMk.le))
        have e12 : Bq * (W k * M k) * (ε * ρ k * W k * M k) = Bq * (ε * ρ k * M k ^ 2) * W k ^ 2 := by ring
        rw [e12] at this
        calc |e k| * |Lh h A Q φ1 k| ≤ Bq * (ε * ρ k * M k ^ 2) * W k ^ 2 := this
          _ ≤ Bq * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) :=
              mul_le_mul_of_nonneg_left hW2 (mul_nonneg hBq0 hX0)
    have := abs_add_le (φ1 k * rt k) (e k * Lh h A Q φ1 k)
    have e13 : (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (ε * ρ k * M k ^ 2)
        = K * Cr * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) + Bq * (ε * ρ k * M k ^ 2) * (CE ^ 2 * W b ^ 2) := by
      ring
    linarith
  have hsum1 : |∑ k ∈ Icc s b, (φ1 k * rt k + e k * Lh h A Q φ1 k)|
      ≤ (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (ε * S) := by
    rw [hεS' ((K * Cr + Bq) * (CE ^ 2 * W b ^ 2))]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun k hk => hterm1 k hk))
  have hh1 : h * |∑ k ∈ Icc s b, (φ1 k * rt k + e k * Lh h A Q φ1 k)|
      ≤ (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (θ * ω) := by
    have := mul_le_mul_of_nonneg_left hsum1 hh.le
    have e15 : h * ((K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (ε * S))
        = (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (θ * ω) := by
      rw [hθω]; ring
    linarith
  have hF1b : |cas A e φ1 (s - 1)| ≤ a * ω * (CE ^ 2 * W b ^ 2) :=
    le_trans hF1 (mul_le_mul_of_nonneg_left (sq_le_of_le_nonneg hV0 (hV b (mem_Icc.mpr ⟨hsb, by omega⟩)) hCE
      (hWpos b (mem_Icc.mpr ⟨hsb, by omega⟩)).le) (mul_nonneg ha hω.le))
  have hcas1 : |cas A e φ1 b| ≤ 2 * CE ^ 2 * (W b) ^ 2 * (ω * (a + K * Cr * θ)) := by
    rw [hX1]
    have hab := abs_sub (cas A e φ1 (s - 1)) (h * ∑ k ∈ Icc s b, (φ1 k * rt k + e k * Lh h A Q φ1 k))
    rw [abs_mul, abs_of_pos hh] at hab
    have e16 : ω * (a + (K * Cr + Bq) * θ) * CE ^ 2 * W b ^ 2 ≤ ω * (2 * (a + K * Cr * θ)) * CE ^ 2 * W b ^ 2 := by
      have := mul_le_mul_of_nonneg_left hGb (mul_nonneg hω.le (mul_nonneg (sq_nonneg CE) (sq_nonneg (W b))))
      nlinarith
    have e17 : a * ω * (CE ^ 2 * W b ^ 2) + (K * Cr + Bq) * (CE ^ 2 * W b ^ 2) * (θ * ω)
        = ω * (a + (K * Cr + Bq) * θ) * CE ^ 2 * W b ^ 2 := by ring
    have e18 : 2 * CE ^ 2 * (W b) ^ 2 * (ω * (a + K * Cr * θ)) = ω * (2 * (a + K * Cr * θ)) * CE ^ 2 * W b ^ 2 := by
      ring
    linarith [hab, hh1, hF1b, e16, e17, e18]
  exact ⟨hbound, hcas2, hcas1⟩

/-- **Flux transfer across an overlap bond.**  If `X_α = ∑_β F_β M_{βα}` with `|det M| ≥ Λ⁻¹`, then the fluxes `F`
of the next patch are bounded by those `X` of the previous one, with the entry weights `W^{±2}`. -/
theorem flux_transfer (Λ CE W ω G X0 X1 F0 F1 m00 m01 m10 m11 : ℝ) (hΛ : 0 < Λ) (hCE : 0 ≤ CE)
    (hW : 0 < W) (hω : 0 ≤ ω) (hG : 0 ≤ G)
    (hdet : Λ⁻¹ ≤ |m00 * m11 - m01 * m10|)
    (h00 : |m00| ≤ Λ) (h11 : |m11| ≤ Λ) (h01 : |m01| ≤ Λ * (W ^ 2)⁻¹) (h10 : |m10| ≤ Λ * W ^ 2)
    (hX0 : |X0| ≤ 2 * CE ^ 2 * W ^ 2 * (ω * G)) (hX1 : |X1| ≤ 2 * ω * G)
    (hr0 : X0 = F0 * m00 + F1 * m10) (hr1 : X1 = F0 * m01 + F1 * m11) :
    |F0| ≤ 2 * Λ ^ 2 * (1 + CE ^ 2) * G * ω * W ^ 2 ∧ |F1| ≤ 2 * Λ ^ 2 * (1 + CE ^ 2) * G * ω := by
  have eF0 : F0 * (m00 * m11 - m01 * m10) = X0 * m11 - X1 * m10 := by
    rw [hr0, hr1]; ring
  have eF1 : F1 * (m00 * m11 - m01 * m10) = -(X0 * m01) + X1 * m00 := by
    rw [hr0, hr1]; ring
  have h1 : 1 ≤ Λ * |m00 * m11 - m01 * m10| := by
    have := mul_le_mul_of_nonneg_left hdet hΛ.le
    rwa [mul_inv_cancel₀ hΛ.ne'] at this
  have hW2 : 0 ≤ W ^ 2 := by positivity
  have hWi : W ^ 2 * (W ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  have hXa : 0 ≤ 2 * CE ^ 2 * W ^ 2 * (ω * G) := by positivity
  have hXb : 0 ≤ 2 * ω * G := by positivity
  constructor
  · have bF0 : |F0| * |m00 * m11 - m01 * m10| ≤ |X0| * |m11| + |X1| * |m10| := by
      rw [← abs_mul, eF0, ← abs_mul, ← abs_mul]
      exact abs_sub _ _ |>.trans_eq (by rw [abs_mul, abs_mul])
    have k0 : |F0| ≤ Λ * (|X0| * |m11| + |X1| * |m10|) := by
      calc |F0| = |F0| * 1 := (mul_one _).symm
        _ ≤ |F0| * (Λ * |m00 * m11 - m01 * m10|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = Λ * (|F0| * |m00 * m11 - m01 * m10|) := by ring
        _ ≤ Λ * (|X0| * |m11| + |X1| * |m10|) := mul_le_mul_of_nonneg_left bF0 hΛ.le
    have b1 : |X0| * |m11| ≤ (2 * CE ^ 2 * W ^ 2 * (ω * G)) * Λ :=
      mul_le_mul hX0 h11 (abs_nonneg _) hXa
    have b2 : |X1| * |m10| ≤ (2 * ω * G) * (Λ * W ^ 2) :=
      mul_le_mul hX1 h10 (abs_nonneg _) hXb
    have : |F0| ≤ Λ * ((2 * CE ^ 2 * W ^ 2 * (ω * G)) * Λ + (2 * ω * G) * (Λ * W ^ 2)) := by
      nlinarith [k0, b1, b2, hΛ]
    have e3 : Λ * ((2 * CE ^ 2 * W ^ 2 * (ω * G)) * Λ + (2 * ω * G) * (Λ * W ^ 2))
        = 2 * Λ ^ 2 * (1 + CE ^ 2) * G * ω * W ^ 2 := by ring
    linarith [this, e3]
  · have bF1 : |F1| * |m00 * m11 - m01 * m10| ≤ |X0| * |m01| + |X1| * |m00| := by
      rw [← abs_mul, eF1]
      calc |-(X0 * m01) + X1 * m00| ≤ |-(X0 * m01)| + |X1 * m00| := abs_add_le _ _
        _ = |X0| * |m01| + |X1| * |m00| := by rw [abs_neg, abs_mul, abs_mul]
    have k1 : |F1| ≤ Λ * (|X0| * |m01| + |X1| * |m00|) := by
      calc |F1| = |F1| * 1 := (mul_one _).symm
        _ ≤ |F1| * (Λ * |m00 * m11 - m01 * m10|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = Λ * (|F1| * |m00 * m11 - m01 * m10|) := by ring
        _ ≤ Λ * (|X0| * |m01| + |X1| * |m00|) := mul_le_mul_of_nonneg_left bF1 hΛ.le
    have c1 : |X0| * |m01| ≤ (2 * CE ^ 2 * W ^ 2 * (ω * G)) * (Λ * (W ^ 2)⁻¹) :=
      mul_le_mul hX0 h01 (abs_nonneg _) hXa
    have c2 : |X1| * |m00| ≤ (2 * ω * G) * Λ := mul_le_mul hX1 h00 (abs_nonneg _) hXb
    have c3 : (2 * CE ^ 2 * W ^ 2 * (ω * G)) * (Λ * (W ^ 2)⁻¹) = 2 * CE ^ 2 * ω * G * Λ := by
      have : (2 * CE ^ 2 * W ^ 2 * (ω * G)) * (Λ * (W ^ 2)⁻¹)
          = 2 * CE ^ 2 * ω * G * Λ * (W ^ 2 * (W ^ 2)⁻¹) := by ring
      rw [this, hWi, mul_one]
    have : |F1| ≤ Λ * (2 * CE ^ 2 * ω * G * Λ + 2 * ω * G * Λ) := by
      rw [c3] at c1
      nlinarith [k1, c1, c2]
    have e4 : Λ * (2 * CE ^ 2 * ω * G * Λ + 2 * ω * G * Λ) = 2 * Λ ^ 2 * (1 + CE ^ 2) * G * ω := by ring
    linarith [this, e4]

/-- The transfer matrix of the overlap bond `j_p`: `U'_{p+1}⁻¹ U_p`, with `U_q` the `2 × 2` matrix of the rows
`(φ¹_q, φ²_q)` at the sites `j, j+1`.  (The paper's `U_{p+1}` must be evaluated at the same bond `j_p`.) -/
noncomputable def bondMat (φ1 φ2 : ℕ → ℤ → ℝ) (p : ℕ) (j : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![φ1 p j, φ2 p j; φ1 p (j + 1), φ2 p (j + 1)]

noncomputable def transMat (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (bondMat φ1 φ2 (p + 1) (jj p))⁻¹ * bondMat φ1 φ2 p (jj p)

/-- Matrix times column vector on `Fin 2 → ℝ`. -/
def mulMV (M : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![M 0 0 * x 0 + M 0 1 * x 1, M 1 0 * x 0 + M 1 1 * x 1]

/-- The coefficient vectors `c_1 = (1,0)`, `c_{p+1} = M_p c_p` (indices as in the paper; `c_0` unused). -/
noncomputable def cvec (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) : ℕ → Fin 2 → ℝ
  | 0 => ![0, 0]
  | 1 => ![1, 0]
  | (n + 2) => mulMV (transMat φ1 φ2 jj (n + 1)) (cvec φ1 φ2 jj (n + 1))

/-- The comparison sequence of patch `p`: `ψ̂_{p,j} = c_{p,1} φ¹_{p,j} + c_{p,2} φ²_{p,j}`. -/
noncomputable def psiHat (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) (j : ℤ) : ℝ :=
  cvec φ1 φ2 jj p 0 * φ1 p j + cvec φ1 φ2 jj p 1 * φ2 p j

lemma cvec_one (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) : cvec φ1 φ2 jj 1 = ![1, 0] := rfl

lemma cvec_succ_succ (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (n : ℕ) :
    cvec φ1 φ2 jj (n + 2) = mulMV (transMat φ1 φ2 jj (n + 1)) (cvec φ1 φ2 jj (n + 1)) := rfl

/-- The determinant of the transfer matrix is nonzero iff the overlap matrix of patch `p+1` is invertible. -/
lemma isUnit_bondMat_of_transMat (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ)
    (hT : (transMat φ1 φ2 jj p).det ≠ 0) : (bondMat φ1 φ2 (p + 1) (jj p)).det ≠ 0 := by
  intro h0
  apply hT
  unfold transMat
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, h0, Ring.inverse_zero, zero_mul]

/-- The entries of the overlap relation `bondMat p j = bondMat (p+1) j * transMat p`. -/
lemma bond_entries (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ)
    (hT : (transMat φ1 φ2 jj p).det ≠ 0) :
    φ1 p (jj p) = φ1 (p + 1) (jj p) * transMat φ1 φ2 jj p 0 0 + φ2 (p + 1) (jj p) * transMat φ1 φ2 jj p 1 0 ∧
    φ2 p (jj p) = φ1 (p + 1) (jj p) * transMat φ1 φ2 jj p 0 1 + φ2 (p + 1) (jj p) * transMat φ1 φ2 jj p 1 1 ∧
    φ1 p (jj p + 1) = φ1 (p + 1) (jj p + 1) * transMat φ1 φ2 jj p 0 0
      + φ2 (p + 1) (jj p + 1) * transMat φ1 φ2 jj p 1 0 ∧
    φ2 p (jj p + 1) = φ1 (p + 1) (jj p + 1) * transMat φ1 φ2 jj p 0 1
      + φ2 (p + 1) (jj p + 1) * transMat φ1 φ2 jj p 1 1 := by
  have hU := isUnit_bondMat_of_transMat φ1 φ2 jj p hT
  have hmat : bondMat φ1 φ2 (p + 1) (jj p) * transMat φ1 φ2 jj p = bondMat φ1 φ2 p (jj p) := by
    unfold transMat
    exact Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr hU)
  have e00 := congrFun (congrFun hmat 0) 0
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  have e11 := congrFun (congrFun hmat 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, bondMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [e00]
  · linarith [e01]
  · linarith [e10]
  · linarith [e11]

/-- **Single-valuedness** of the comparison sequence on an overlap bond: `ψ̂_p = ψ̂_{p+1}` at the sites `j` where the
patch `p` is the change of basis `M_p` of patch `p+1`. -/
lemma psiHat_overlap (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p) (j : ℤ)
    (hr1 : φ1 p j = φ1 (p + 1) j * transMat φ1 φ2 jj p 0 0 + φ2 (p + 1) j * transMat φ1 φ2 jj p 1 0)
    (hr2 : φ2 p j = φ1 (p + 1) j * transMat φ1 φ2 jj p 0 1 + φ2 (p + 1) j * transMat φ1 φ2 jj p 1 1) :
    psiHat φ1 φ2 jj p j = psiHat φ1 φ2 jj (p + 1) j := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hc : cvec φ1 φ2 jj (n + 1 + 1) = mulMV (transMat φ1 φ2 jj (n + 1)) (cvec φ1 φ2 jj (n + 1)) := rfl
  unfold psiHat
  rw [hc]
  simp only [mulMV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hr1, hr2]
  ring

/-- **Coefficient growth** (`c_{p,1}`, `c_{p,2}` of the paper): `|c_{p,1}| ≤ X^{p-1}`, `|c_{p,2}| ≤ X^{p-1} W_{j_{p-1}}²`
with `X = Λ(1+C_E²)`; the transfer condition (S3) and the monotonicity of the weights are used. -/
theorem cvec_bounds (Λ CE : ℝ) (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (W : ℤ → ℝ) (P : ℕ)
    (hΛ : 1 ≤ Λ) (hCE : 0 ≤ CE)
    (hWj : ∀ p, p ≤ P → 0 < W (jj p))
    (hmonoj : ∀ p, 1 ≤ p → p ≤ P → W (jj (p - 1)) ≤ CE * W (jj p))
    (hT : ∀ p, 1 ≤ p → p < P → Λ⁻¹ ≤ |(transMat φ1 φ2 jj p).det| ∧ |transMat φ1 φ2 jj p 0 0| ≤ Λ ∧
      |transMat φ1 φ2 jj p 1 1| ≤ Λ ∧ |transMat φ1 φ2 jj p 0 1| ≤ Λ * (W (jj p) ^ 2)⁻¹ ∧
      |transMat φ1 φ2 jj p 1 0| ≤ Λ * W (jj p) ^ 2) :
    ∀ n : ℕ, n + 1 ≤ P →
      |cvec φ1 φ2 jj (n + 1) 0| ≤ (Λ * (1 + CE ^ 2)) ^ n ∧
      |cvec φ1 φ2 jj (n + 1) 1| ≤ (Λ * (1 + CE ^ 2)) ^ n * W (jj n) ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [show (0 : ℕ) + 1 = 1 from rfl, cvec_one]
    constructor
    · simp
    · have h0 : |(![1, 0] : Fin 2 → ℝ) 1| = 0 := by simp
      rw [h0, pow_zero, one_mul]
      positivity
  | succ n ih =>
    intro hP
    obtain ⟨ih0, ih1⟩ := ih (by omega)
    have hc : cvec φ1 φ2 jj (n + 1 + 1) = mulMV (transMat φ1 φ2 jj (n + 1)) (cvec φ1 φ2 jj (n + 1)) := rfl
    obtain ⟨_, hM00, hM11, hM01, hM10⟩ := hT (n + 1) (by omega) (by omega)
    have hWb : 0 < W (jj (n + 1)) := hWj (n + 1) (by omega)
    have hWa : 0 < W (jj n) := hWj n (by omega)
    have hm := hmonoj (n + 1) (by omega) (by omega)
    have hm' : W (jj n) ^ 2 ≤ CE ^ 2 * W (jj (n + 1)) ^ 2 := by
      simp only [Nat.add_sub_cancel] at hm
      exact sq_le_of_le_nonneg hWa.le hm hCE hWb.le
    set X := Λ * (1 + CE ^ 2) with hX
    have hX0 : 0 ≤ X := by positivity
    have hXn : 0 ≤ X ^ n := pow_nonneg hX0 n
    have hΛ0 : 0 ≤ Λ := by linarith
    have hWb2 : 0 < W (jj (n + 1)) ^ 2 := by positivity
    have hWi : W (jj (n + 1)) ^ 2 * (W (jj (n + 1)) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hWb2.ne'
    rw [hc]
    simp only [mulMV, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    constructor
    · -- the first component
      have b1 : |transMat φ1 φ2 jj (n + 1) 0 0 * cvec φ1 φ2 jj (n + 1) 0| ≤ Λ * X ^ n := by
        rw [abs_mul]
        exact mul_le_mul hM00 ih0 (abs_nonneg _) hΛ0
      have b2 : |transMat φ1 φ2 jj (n + 1) 0 1 * cvec φ1 φ2 jj (n + 1) 1|
          ≤ Λ * (W (jj (n + 1)) ^ 2)⁻¹ * (X ^ n * W (jj n) ^ 2) := by
        rw [abs_mul]
        exact mul_le_mul hM01 ih1 (abs_nonneg _) (by positivity)
      have b3 : Λ * (W (jj (n + 1)) ^ 2)⁻¹ * (X ^ n * W (jj n) ^ 2) ≤ Λ * CE ^ 2 * X ^ n := by
        have : Λ * (W (jj (n + 1)) ^ 2)⁻¹ * (X ^ n * W (jj n) ^ 2)
            ≤ Λ * (W (jj (n + 1)) ^ 2)⁻¹ * (X ^ n * (CE ^ 2 * W (jj (n + 1)) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm' hXn) (by positivity)
        have e : Λ * (W (jj (n + 1)) ^ 2)⁻¹ * (X ^ n * (CE ^ 2 * W (jj (n + 1)) ^ 2))
            = Λ * CE ^ 2 * X ^ n * ((W (jj (n + 1)) ^ 2)⁻¹ * W (jj (n + 1)) ^ 2) := by ring
        rw [e, inv_mul_cancel₀ hWb2.ne', mul_one] at this
        exact this
      have hpow : X ^ (n + 1) = X ^ n * (Λ * (1 + CE ^ 2)) := by rw [pow_succ]
      calc |transMat φ1 φ2 jj (n + 1) 0 0 * cvec φ1 φ2 jj (n + 1) 0
            + transMat φ1 φ2 jj (n + 1) 0 1 * cvec φ1 φ2 jj (n + 1) 1|
          ≤ |transMat φ1 φ2 jj (n + 1) 0 0 * cvec φ1 φ2 jj (n + 1) 0|
            + |transMat φ1 φ2 jj (n + 1) 0 1 * cvec φ1 φ2 jj (n + 1) 1| := abs_add_le _ _
        _ ≤ Λ * X ^ n + Λ * CE ^ 2 * X ^ n := add_le_add b1 (le_trans b2 b3)
        _ = X ^ (n + 1) := by rw [hpow, hX]; ring
    · -- the second component
      have b1 : |transMat φ1 φ2 jj (n + 1) 1 0 * cvec φ1 φ2 jj (n + 1) 0|
          ≤ (Λ * W (jj (n + 1)) ^ 2) * X ^ n := by
        rw [abs_mul]
        exact mul_le_mul hM10 ih0 (abs_nonneg _) (by positivity)
      have b2 : |transMat φ1 φ2 jj (n + 1) 1 1 * cvec φ1 φ2 jj (n + 1) 1|
          ≤ Λ * (X ^ n * W (jj n) ^ 2) := by
        rw [abs_mul]
        exact mul_le_mul hM11 ih1 (abs_nonneg _) hΛ0
      have b3 : Λ * (X ^ n * W (jj n) ^ 2) ≤ Λ * (X ^ n * (CE ^ 2 * W (jj (n + 1)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm' hXn) hΛ0
      have hpow : X ^ (n + 1) * W (jj (n + 1)) ^ 2
          = (Λ * W (jj (n + 1)) ^ 2) * X ^ n + Λ * (X ^ n * (CE ^ 2 * W (jj (n + 1)) ^ 2)) := by
        rw [pow_succ, hX]; ring
      calc |transMat φ1 φ2 jj (n + 1) 1 0 * cvec φ1 φ2 jj (n + 1) 0
            + transMat φ1 φ2 jj (n + 1) 1 1 * cvec φ1 φ2 jj (n + 1) 1|
          ≤ |transMat φ1 φ2 jj (n + 1) 1 0 * cvec φ1 φ2 jj (n + 1) 0|
            + |transMat φ1 φ2 jj (n + 1) 1 1 * cvec φ1 φ2 jj (n + 1) 1| := abs_add_le _ _
        _ ≤ (Λ * W (jj (n + 1)) ^ 2) * X ^ n + Λ * (X ^ n * (CE ^ 2 * W (jj (n + 1)) ^ 2)) :=
            add_le_add b1 (le_trans b2 b3)
        _ = X ^ (n + 1) * W (jj (n + 1)) ^ 2 := hpow.symm

/-! ### Assembly: the multi-patch theorem -/

lemma jj_mono_le (jj : ℕ → ℤ) (P : ℕ) (hjjmono : ∀ p < P, jj p < jj (p + 1)) :
    ∀ p q : ℕ, p ≤ q → q ≤ P → jj p ≤ jj q := by
  intro p q hpq hqP
  induction q, hpq using Nat.le_induction with
  | base => exact le_rfl
  | succ q hpq ih => exact (ih (by omega)).trans (le_of_lt (hjjmono q (by omega)))

/-- The first equation site of patch `p`: the seed site `s₀` for `p = 1`, the site `j_{p-1}+1` for `p ≥ 2`. -/
def eqLo (s0 : ℤ) (jj : ℕ → ℤ) (p : ℕ) : ℤ := if p = 1 then s0 else jj (p - 1) + 1

/-- The modulus sum `Θ = (h/ω) ∑_p ∑_{k ∈ I_p°} ρ_k 𝖬_k²` of `thm:eng-volterra`(a). -/
noncomputable def volTheta (h ω : ℝ) (s0 : ℤ) (jj : ℕ → ℤ) (P : ℕ) (ρ M : ℤ → ℝ) : ℝ :=
  h / ω * ∑ p ∈ Icc 1 P, ∑ k ∈ Icc (eqLo s0 jj p) (jj p), ρ k * M k ^ 2

/-- `κ = 2 Λ²(1 + C_E²)`: the gain of one overlap bond. -/
noncomputable def mvKappa (Λ CE : ℝ) : ℝ := 2 * Λ ^ 2 * (1 + CE ^ 2)

/-- `C_r* = (Λ(1+C_E²))^P (1+C_E²)`: a bound for the residual coefficients of all patches. -/
noncomputable def mvCrStar (Λ CE : ℝ) (P : ℕ) : ℝ := (Λ * (1 + CE ^ 2)) ^ P * (1 + CE ^ 2)

/-- The constant `C = 2 D K² C_r* ((κ+1)^P + 1)` with `D = (1+C_E²)/c₋`. -/
noncomputable def mvC (cm CE K Λ : ℝ) (P : ℕ) : ℝ :=
  2 * ((1 + CE ^ 2) / cm) * K * (K * mvCrStar Λ CE P * ((mvKappa Λ CE + 1) ^ P + 1))

/-- The smallness threshold `c* = 1/(2DK + 1)`. -/
noncomputable def mvCstar (cm CE K : ℝ) : ℝ := 1 / (2 * ((1 + CE ^ 2) / cm) * K + 1)

lemma eqLo_one (s0 : ℤ) (jj : ℕ → ℤ) : eqLo s0 jj 1 = s0 := by simp [eqLo]

lemma eqLo_succ (s0 : ℤ) (jj : ℕ → ℤ) (p : ℕ) (hp : 1 ≤ p) : eqLo s0 jj (p + 1) = jj p + 1 := by
  have : p + 1 ≠ 1 := by omega
  unfold eqLo
  rw [if_neg this, Nat.add_sub_cancel]

/-- The residual of the error of patch `p` on its equation sites (`rt` the combination of the patch residuals). -/
lemma residual_error (h : ℝ) (hh : h ≠ 0) (A Q ψ φ1 φ2 : ℤ → ℝ) (c0 c1 : ℝ) (k : ℤ)
    (hψ : Lh h A Q ψ k = 0) :
    Lop A Q (fun j => ψ j - (c0 * φ1 j + c1 * φ2 j)) k
      = -(h * (c0 * Lh h A Q φ1 k + c1 * Lh h A Q φ2 k)) := by
  have hsplit : Lop A Q (fun j => ψ j - (c0 * φ1 j + c1 * φ2 j)) k
      = Lop A Q ψ k - (c0 * Lop A Q φ1 k + c1 * Lop A Q φ2 k) := by
    simp only [Lop]
    ring
  rw [hsplit, Lop_eq_h_mul_Lh h hh A Q ψ k, hψ, Lop_eq_h_mul_Lh h hh A Q φ1 k,
    Lop_eq_h_mul_Lh h hh A Q φ2 k]
  ring

/-- Entry of the Casoratian under the change of basis: `𝒲(e, φ^α_p) = ∑_β M_{βα} 𝒲(e, φ^β_{p+1})` at the bond,
given the row relations at the two sites of the bond. -/
lemma cas_transfer_rel (A e u v u' v' : ℤ → ℝ) (j : ℤ) (m00 m01 m10 m11 : ℝ)
    (hu0 : u j = u' j * m00 + v' j * m10) (hu1 : u (j + 1) = u' (j + 1) * m00 + v' (j + 1) * m10)
    (hv0 : v j = u' j * m01 + v' j * m11) (hv1 : v (j + 1) = u' (j + 1) * m01 + v' (j + 1) * m11) :
    cas A e u j = cas A e u' j * m00 + cas A e v' j * m10 ∧
    cas A e v j = cas A e u' j * m01 + cas A e v' j * m11 := by
  constructor
  · unfold cas
    rw [hu0, hu1]
    ring
  · unfold cas
    rw [hv0, hv1]
    ring

/-- The Casoratian at a bond depends only on the error at its two sites. -/
lemma cas_congr_e (A e e' f : ℤ → ℝ) (j : ℤ) (h0 : e j = e' j) (h1 : e (j + 1) = e' (j + 1)) :
    cas A e f j = cas A e' f j := by
  unfold cas
  rw [h0, h1]

lemma cas_zero_entry (A e f : ℤ → ℝ) (s0 : ℤ) (hs0 : s0 = 0 ∨ s0 = 1) (hA : s0 = 0 → A (-1) = 0)
    (he : ∀ j, 0 ≤ j → j ≤ s0 → e j = 0) : cas A e f (s0 - 1) = 0 := by
  rcases hs0 with h0 | h1
  · subst h0
    have := cas_hard_edge A e f (hA rfl)
    simpa using this
  · subst h1
    have e0 := he 0 le_rfl (by norm_num)
    have e1 := he 1 (by norm_num) le_rfl
    norm_num [cas, e0, e1]

/-- The residual coefficient bound: `|c_{p,1} u + c_{p,2} v| ≤ X^n (1+C_E²) ε ρ W M` for the patch `n+1`. -/
lemma rt_bound (ε CE X c0 c1 u v Wa Wk Mk ρk : ℝ) (n : ℕ) (hX : 1 ≤ X) (hCE : 0 ≤ CE) (hε : 0 ≤ ε)
    (hρ : 0 ≤ ρk) (hWk : 0 < Wk) (hMk : 0 ≤ Mk) (hWa : 0 < Wa) (hWak : n ≠ 0 → Wa ≤ CE * Wk)
    (hc0 : |c0| ≤ X ^ n) (hc1 : |c1| ≤ X ^ n * Wa ^ 2) (hc1z : n = 0 → c1 = 0)
    (hu : |u| ≤ ε * ρk * Wk * Mk) (hv : n ≠ 0 → |v| ≤ ε * ρk * Wk⁻¹ * Mk) :
    |c0 * u + c1 * v| ≤ X ^ n * (1 + CE ^ 2) * (ε * ρk * Wk * Mk) := by
  have hXn : 0 ≤ X ^ n := pow_nonneg (by linarith) n
  have hE : 0 ≤ ε * ρk * Wk * Mk := by positivity
  have t0 : |c0 * u| ≤ X ^ n * (ε * ρk * Wk * Mk) := by
    rw [abs_mul]
    exact mul_le_mul hc0 hu (abs_nonneg _) (by positivity)
  by_cases hn : n = 0
  · have hc : c1 = 0 := hc1z hn
    rw [hc, zero_mul, add_zero]
    have : X ^ n * (ε * ρk * Wk * Mk) ≤ X ^ n * (1 + CE ^ 2) * (ε * ρk * Wk * Mk) := by
      have : X ^ n * (1 + CE ^ 2) * (ε * ρk * Wk * Mk) = X ^ n * (ε * ρk * Wk * Mk) * (1 + CE ^ 2) := by ring
      rw [this]
      have hpos : 0 ≤ X ^ n * (ε * ρk * Wk * Mk) := mul_nonneg hXn hE
      nlinarith [sq_nonneg CE]
    exact le_trans t0 this
  · have hWkk : Wa ≤ CE * Wk := hWak hn
    have t1 : |c1 * v| ≤ X ^ n * CE ^ 2 * (ε * ρk * Wk * Mk) := by
      rw [abs_mul]
      have hv' := hv hn
      have hb : |c1| * |v| ≤ (X ^ n * Wa ^ 2) * (ε * ρk * Wk⁻¹ * Mk) :=
        mul_le_mul hc1 hv' (abs_nonneg _) (by positivity)
      have hsq : Wa ^ 2 ≤ CE ^ 2 * Wk ^ 2 := by
        have := mul_le_mul hWkk hWkk hWa.le (by positivity)
        nlinarith
      have hfin : (X ^ n * Wa ^ 2) * (ε * ρk * Wk⁻¹ * Mk) ≤ X ^ n * (CE ^ 2 * Wk ^ 2) * (ε * ρk * Wk⁻¹ * Mk) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hsq hXn
      have heq : X ^ n * (CE ^ 2 * Wk ^ 2) * (ε * ρk * Wk⁻¹ * Mk) = X ^ n * CE ^ 2 * (ε * ρk * Wk * Mk) * (Wk * Wk⁻¹) := by
        ring
      rw [heq, mul_inv_cancel₀ hWk.ne', mul_one] at hfin
      linarith [hb, hfin]
    have : X ^ n * (1 + CE ^ 2) * (ε * ρk * Wk * Mk) = X ^ n * (ε * ρk * Wk * Mk) + X ^ n * CE ^ 2 * (ε * ρk * Wk * Mk) := by
      ring
    calc |c0 * u + c1 * v| ≤ |c0 * u| + |c1 * v| := abs_add_le _ _
      _ ≤ X ^ n * (ε * ρk * Wk * Mk) + X ^ n * CE ^ 2 * (ε * ρk * Wk * Mk) := add_le_add t0 t1
      _ = X ^ n * (1 + CE ^ 2) * (ε * ρk * Wk * Mk) := this.symm

/-- The numerical step of the induction on the patches: `κ(c q^p Y + c θ) ≤ c q^{p+1} Y` for `q = κ+1`, `θ ≤ Y`. -/
lemma kappa_step (κ c Y θ : ℝ) (p : ℕ) (hκ : 0 ≤ κ) (hc : 0 ≤ c) (hY : 0 ≤ Y) (hθ0 : 0 ≤ θ) (hθY : θ ≤ Y)
    (hp : 1 ≤ p) :
    κ * (c * (κ + 1) ^ p * Y + c * θ) ≤ c * (κ + 1) ^ (p + 1) * Y := by
  have hq : κ + 1 ≤ (κ + 1) ^ p := by
    calc κ + 1 = (κ + 1) ^ 1 := (pow_one _).symm
      _ ≤ (κ + 1) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hqp : κ ≤ (κ + 1) ^ p := by linarith
  have hθ : c * θ ≤ c * Y := mul_le_mul_of_nonneg_left hθY hc
  have h1 : κ * (c * (κ + 1) ^ p * Y + c * θ) ≤ κ * (c * (κ + 1) ^ p * Y + c * Y) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ
  have h2 : c * (κ + 1) ^ (p + 1) * Y = c * Y * ((κ + 1) ^ p * (κ + 1)) := by ring
  have h3 : κ * (c * (κ + 1) ^ p * Y + c * Y) ≤ c * Y * ((κ + 1) ^ p * (κ + 1)) := by
    have hcY : 0 ≤ c * Y := mul_nonneg hc hY
    have : κ * (c * (κ + 1) ^ p * Y + c * Y) = c * Y * (κ * (κ + 1) ^ p + κ) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ hcY
    have : (κ + 1) ^ p * (κ + 1) = (κ + 1) ^ p * κ + (κ + 1) ^ p := by ring
    rw [this]
    nlinarith [hqp]
  rw [h2]
  exact le_trans h1 h3

/-- Covering: every site `j ∈ [s₀, N_R]` lies in some `[eqLo p, j_p + 1]`, `1 ≤ p ≤ P`. -/
lemma covering_patch (s0 NR : ℤ) (P : ℕ) (jj : ℕ → ℤ) (hP : 1 ≤ P) (hjj0 : jj 0 = 0)
    (hjjP : jj P = NR - 1) (j : ℤ) (hs : s0 ≤ j) (hjN : j ≤ NR) :
    ∃ p, 1 ≤ p ∧ p ≤ P ∧ eqLo s0 jj p ≤ j ∧ j ≤ jj p + 1 := by
  classical
  have hex : ∃ p, 1 ≤ p ∧ j ≤ jj p + 1 := ⟨P, hP, by rw [hjjP]; omega⟩
  obtain ⟨hp1, hpj⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ P := Nat.find_min' hex ⟨hP, by rw [hjjP]; omega⟩
  refine ⟨Nat.find hex, hp1, hle, ?_, hpj⟩
  by_cases h1 : Nat.find hex = 1
  · rw [h1, eqLo_one]
    exact hs
  · have hge : 2 ≤ Nat.find hex := by omega
    have hmin : ¬ (1 ≤ Nat.find hex - 1 ∧ j ≤ jj (Nat.find hex - 1) + 1) :=
      Nat.find_min hex (by omega)
    have hq : j > jj (Nat.find hex - 1) + 1 := by
      by_contra hc
      exact hmin ⟨by omega, by omega⟩
    have e1 : eqLo s0 jj (Nat.find hex) = jj (Nat.find hex - 1) + 1 := by
      unfold eqLo
      rw [if_neg h1]
    rw [e1]
    omega

/-- **Multi-patch Casoratian--Volterra stability** (`thm:eng-volterra`(a), general `P`, both seeds).

Data: the patch breakpoints `jj p = j_p` (`j_0 = 0 < j_1 < ⋯ < j_P = N_R - 1`), the pairs `φ¹_p, φ²_p` (functions of the
site `j`, used on the window `[j_{p-1}, j_p + 1]`), the bond coefficients `A`, `Q`, the envelopes `M, W` and the
residual weight `ρ` (global).  The seed is `s₀ ∈ {0, 1}`: `s₀ = 0` is the hard edge (`A(-1) = 0`, seed `ψ₀`, equation
sites `[0, N_R-1]`); `s₀ = 1` is the two-node seed (seed `ψ₀, ψ₁`, equation sites `[1, N_R-1]`).  The transfer matrix of
the overlap `j_p` is `M_p = (𝐔_{p+1})⁻¹ 𝐔_p` with `𝐔_q` the matrix of the pair of patch `q` at the sites `j_p, j_p+1`
(see `transMat`).  Conclusions: the bound `|ψ_j - ψ̂_{p,j}| ≤ C ε Θ W_j M_j` on every patch window, the single-valuedness of
`ψ̂` on the overlaps, and the global bound for every `j ∈ [0, N_R]` with a patch `p`. -/
theorem volterra_multi (h ω cm CE K ε Λ : ℝ) (A Q ψ ρ M W : ℤ → ℝ) (s0 NR : ℤ) (P : ℕ)
    (jj : ℕ → ℤ) (φ1 φ2 : ℕ → ℤ → ℝ)
    (hh : 0 < h) (hω : 0 < ω) (hcm : 0 < cm) (hK : 0 ≤ K) (hε : 0 ≤ ε) (hΛ : 1 ≤ Λ)
    (hP : 1 ≤ P) (hjj0 : jj 0 = 0) (hjjmono : ∀ p < P, jj p < jj (p + 1)) (hjjP : jj P = NR - 1)
    (hs0 : s0 = 0 ∨ s0 = 1) (hA : s0 = 0 → A (-1) = 0)
    (hS1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p), cm * ω ≤ |cas A (φ1 p) (φ2 p) j|)
    (hMpos : ∀ j ∈ Icc 0 NR, 0 < M j) (hWpos : ∀ j ∈ Icc 0 NR, 0 < W j)
    (hmono : ∀ k ∈ Icc 0 NR, ∀ j ∈ Icc 0 NR, k ≤ j → W k ≤ CE * W j)
    (hφ1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1), |φ1 p j| ≤ K * W j * M j)
    (hφ2 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1), |φ2 p j| ≤ K * (W j)⁻¹ * M j)
    (hρ : ∀ k, 0 ≤ ρ k)
    (hr1 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), |Lh h A Q (φ1 p) k| ≤ ε * ρ k * W k * M k)
    (hr2 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k ≠ 0 →
      |Lh h A Q (φ2 p) k| ≤ ε * ρ k * (W k)⁻¹ * M k)
    (hT : ∀ p, 1 ≤ p → p < P → Λ⁻¹ ≤ |(transMat φ1 φ2 jj p).det| ∧
      |transMat φ1 φ2 jj p 0 0| ≤ Λ ∧ |transMat φ1 φ2 jj p 1 1| ≤ Λ ∧
      |transMat φ1 φ2 jj p 0 1| ≤ Λ * (W (jj p) ^ 2)⁻¹ ∧ |transMat φ1 φ2 jj p 1 0| ≤ Λ * W (jj p) ^ 2)
    (hsol : ∀ k ∈ Icc s0 (NR - 1), Lh h A Q ψ k = 0)
    (hseed : ∀ j ∈ Icc 0 s0, ψ j = φ1 1 j)
    (hsmall : ε * volTheta h ω s0 jj P ρ M ≤ mvCstar cm CE K) :
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |ψ j - psiHat φ1 φ2 jj p j| ≤ mvC cm CE K Λ P * (ε * volTheta h ω s0 jj P ρ M) * W j * M j) ∧
    (∀ p, 1 ≤ p → p < P → ∀ j ∈ Icc (jj p) (jj p + 1),
      psiHat φ1 φ2 jj p j = psiHat φ1 φ2 jj (p + 1) j) ∧
    (∀ j ∈ Icc 0 NR, ∃ p ∈ Icc 1 P,
      |ψ j - psiHat φ1 φ2 jj p j| ≤ mvC cm CE K Λ P * (ε * volTheta h ω s0 jj P ρ M) * W j * M j) := by
  classical
  -- basic facts on the breakpoints and the seed
  have hjjle : ∀ p, p ≤ P → jj p ≤ NR - 1 := fun p hp => by
    have := jj_mono_le jj P hjjmono p P hp le_rfl
    rw [hjjP] at this
    exact this
  have hjjge : ∀ p, p ≤ P → 0 ≤ jj p := fun p hp => by
    have := jj_mono_le jj P hjjmono 0 p (Nat.zero_le _) hp
    rw [hjj0] at this
    exact this
  have hNR : 1 ≤ NR := by
    have h1 := hjjge P le_rfl
    rw [hjjP] at h1
    omega
  have hs0nn : 0 ≤ s0 := by rcases hs0 with h0 | h0 <;> omega
  have hs0le : s0 ≤ 1 := by rcases hs0 with h0 | h0 <;> omega
  have hsite : ∀ p, p ≤ P → 0 ≤ jj p ∧ jj p + 1 ≤ NR := fun p hp =>
    ⟨hjjge p hp, by have := hjjle p hp; omega⟩
  have hmemNR : ∀ j, 0 ≤ j → j ≤ NR → j ∈ Icc 0 NR := fun j h0 h1 => mem_Icc.mpr ⟨h0, h1⟩
  have hCE0 : 0 ≤ CE := by
    have hw := hWpos 0 (mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have := hmono 0 (mem_Icc.mpr ⟨le_rfl, by omega⟩) 0 (mem_Icc.mpr ⟨le_rfl, by omega⟩) le_rfl
    nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hX1 : 1 ≤ Λ * (1 + CE ^ 2) := by nlinarith [sq_nonneg CE]
  have hD0 : 0 ≤ (1 + CE ^ 2) / cm := by positivity
  -- the monotone weights on the breakpoints
  have hWj : ∀ p, p ≤ P → 0 < W (jj p) := fun p hp =>
    hWpos (jj p) (hmemNR _ (hsite p hp).1 (by have := (hsite p hp).2; omega))
  have hmonoj : ∀ p, 1 ≤ p → p ≤ P → W (jj (p - 1)) ≤ CE * W (jj p) := by
    intro p hp1 hpP
    have hle : jj (p - 1) ≤ jj p := by
      have := jj_mono_le jj P hjjmono (p - 1) p (by omega) hpP
      exact this
    exact hmono (jj (p - 1)) (hmemNR _ (hsite (p - 1) (by omega)).1 (by have := (hsite (p - 1) (by omega)).2; omega))
      (jj p) (hmemNR _ (hsite p hpP).1 (by have := (hsite p hpP).2; omega)) hle
  -- the coefficients
  have hcvb := cvec_bounds Λ CE φ1 φ2 jj W P hΛ hCE0 hWj hmonoj hT
  -- the constants
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = volTheta h ω s0 jj P ρ M := ⟨_, rfl⟩
  rw [← hΘ] at hsmall ⊢
  have hΘ0 : 0 ≤ Θ := by
    rw [hΘ, volTheta]
    apply mul_nonneg (div_nonneg hh.le hω.le)
    exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun k _ => mul_nonneg (hρ k) (sq_nonneg _)))
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ε * Θ := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact mul_nonneg hε hΘ0
  have hsY : Y ≤ mvCstar cm CE K := by rw [hY]; exact hsmall
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = mvKappa Λ CE := ⟨_, rfl⟩
  have hκe : κ = 2 * Λ ^ 2 * (1 + CE ^ 2) := by rw [hκ]; rfl
  have hκ0 : 0 ≤ κ := by rw [hκe]; positivity
  obtain ⟨CrS, hCrS⟩ : ∃ C, C = mvCrStar Λ CE P := ⟨_, rfl⟩
  have hCrS0 : 0 ≤ CrS := by rw [hCrS]; unfold mvCrStar; positivity
  obtain ⟨ap, hap⟩ : ∃ a : ℕ → ℝ, ∀ p, a p = K * CrS * (κ + 1) ^ p * Y := ⟨fun p => K * CrS * (κ + 1) ^ p * Y, fun _ => rfl⟩
  have hap0 : ∀ p, 0 ≤ ap p := fun p => by
    rw [hap]; positivity
  obtain ⟨Vp, hVp⟩ : ∃ V : ℕ → ℝ, ∀ p, V p = if p = 1 then 0 else W (jj (p - 1)) := ⟨_, fun _ => rfl⟩
  have hVp0 : ∀ p, 1 ≤ p → p ≤ P → 0 ≤ Vp p := by
    intro p hp1 hpP
    rw [hVp]
    split_ifs
    · exact le_rfl
    · exact (hWj (p - 1) (by omega)).le
  have hjjle2 : ∀ p, 1 ≤ p → p ≤ P → jj (p - 1) ≤ jj p := fun p hp1 hpP => by
    have := jj_mono_le jj P hjjmono (p - 1) p (by omega) hpP
    exact this
  -- the error, the residual coefficients and the modulus sums per patch
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℤ → ℝ, ∀ p j, e p j = ψ j - psiHat φ1 φ2 jj p j :=
    ⟨fun p j => ψ j - psiHat φ1 φ2 jj p j, fun _ _ => rfl⟩
  obtain ⟨rt, hrt⟩ : ∃ rt : ℕ → ℤ → ℝ, ∀ p k, rt p k = cvec φ1 φ2 jj p 0 * Lh h A Q (φ1 p) k
      + cvec φ1 φ2 jj p 1 * Lh h A Q (φ2 p) k := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Sp, hSp⟩ : ∃ S : ℕ → ℝ, ∀ p, S p = ∑ k ∈ Icc (eqLo s0 jj p) (jj p), ρ k * M k ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hSp0 : ∀ p, 0 ≤ Sp p := fun p => by
    rw [hSp]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hρ k) (sq_nonneg _))
  have hΘeq : Θ = h / ω * ∑ p ∈ Icc 1 P, Sp p := by
    rw [hΘ, volTheta]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (hSp p).symm)
  have hthY0 : ∀ p ∈ Icc 1 P, True := fun _ _ => trivial
  obtain ⟨th, hth⟩ : ∃ t : ℕ → ℝ, ∀ p, t p = ε * (h * Sp p) / ω := ⟨_, fun _ => rfl⟩
  have hth0 : ∀ p, 0 ≤ th p := fun p => by
    rw [hth]
    exact div_nonneg (mul_nonneg hε (mul_nonneg hh.le (hSp0 p))) hω.le
  have hthω : ∀ p, th p * ω = ε * (h * Sp p) := fun p => by
    rw [hth]
    field_simp
  have hthY : ∀ p ∈ Icc 1 P, th p ≤ Y := by
    intro p hp
    have hle : h / ω * Sp p ≤ Θ := by
      rw [hΘeq]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun q _ => hSp0 q) hp) (div_nonneg hh.le hω.le)
    rw [hth, hY]
    have e1 : ε * (h * Sp p) / ω = ε * (h / ω * Sp p) := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hle hε
  have hsmallth : ∀ p ∈ Icc 1 P, 2 * ((1 + CE ^ 2) / cm) * K * th p ≤ 1 := by
    intro p hp
    have hc0 : 0 ≤ 2 * ((1 + CE ^ 2) / cm) * K := by positivity
    have t1 : 2 * ((1 + CE ^ 2) / cm) * K * th p ≤ 2 * ((1 + CE ^ 2) / cm) * K * Y :=
      mul_le_mul_of_nonneg_left (hthY p hp) hc0
    have t2 : 2 * ((1 + CE ^ 2) / cm) * K * Y ≤ 2 * ((1 + CE ^ 2) / cm) * K * mvCstar cm CE K :=
      mul_le_mul_of_nonneg_left hsY hc0
    have t3 : 2 * ((1 + CE ^ 2) / cm) * K * mvCstar cm CE K ≤ 1 := by
      unfold mvCstar
      rw [mul_one_div, div_le_one (by positivity)]
      linarith
    linarith
  -- the seed: the error vanishes on the seed sites
  have he_seed : ∀ j ∈ Icc 0 s0, e 1 j = 0 := by
    intro j hj
    rw [he, hseed j hj]
    simp [psiHat, cvec_one]
  -- the sites of patch `p`
  have hlo : ∀ p, 1 ≤ p → p ≤ P → jj (p - 1) ≤ eqLo s0 jj p ∧ eqLo s0 jj p ≤ jj p ∧ 0 ≤ eqLo s0 jj p ∧
      s0 ≤ eqLo s0 jj p ∧ (p ≠ 1 → 1 ≤ eqLo s0 jj p) := by
    intro p hp1 hpP
    by_cases hp : p = 1
    · subst hp
      rw [eqLo_one]
      have h10 : jj (1 - 1) = 0 := by simp [hjj0]
      have h11 : jj 0 < jj 1 := hjjmono 0 (by omega)
      rw [hjj0] at h11
      refine ⟨by rw [h10]; exact hs0nn, by omega, hs0nn, le_rfl, fun h' => absurd rfl h'⟩
    · have hl : eqLo s0 jj p = jj (p - 1) + 1 := by
        unfold eqLo
        rw [if_neg hp]
      have hm : jj (p - 1) + 1 ≤ jj p := by
        have := hjjmono (p - 1) (by omega)
        rw [show p - 1 + 1 = p by omega] at this
        omega
      rw [hl]
      have hj0 := hjjge (p - 1) (by omega)
      exact ⟨by omega, hm, by omega, by omega, fun _ => by omega⟩
  -- the entry bounds, the interior bounds and the exit fluxes of patch `p`
  have hpatch : ∀ p, 1 ≤ p → p ≤ P →
      |cas A (e p) (φ2 p) (eqLo s0 jj p - 1)| ≤ ap p * ω →
      |cas A (e p) (φ1 p) (eqLo s0 jj p - 1)| ≤ ap p * ω * (Vp p) ^ 2 →
      (∀ m ∈ Icc (eqLo s0 jj p) (jj p + 1),
          |e p m| ≤ 2 * ((1 + CE ^ 2) / cm) * K * (ap p + K * CrS * th p) * (W m * M m)) ∧
      |cas A (e p) (φ2 p) (jj p)| ≤ 2 * ω * (ap p + K * CrS * th p) ∧
      |cas A (e p) (φ1 p) (jj p)| ≤ 2 * CE ^ 2 * (W (jj p)) ^ 2 * (ω * (ap p + K * CrS * th p)) := by
    intro p hp1 hpP E2 E1
    have hmem : p ∈ Icc 1 P := mem_Icc.mpr ⟨hp1, hpP⟩
    obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hlo p hp1 hpP
    have hsubW : Icc (eqLo s0 jj p) (jj p + 1) ⊆ Icc 0 NR := fun j hj =>
      mem_Icc.mpr ⟨le_trans hl3 (mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; have := (hsite p hpP).2; omega⟩
    have hsubA : Icc (eqLo s0 jj p) (jj p + 1) ⊆ Icc (jj (p - 1)) (jj p + 1) := fun j hj =>
      mem_Icc.mpr ⟨le_trans hl1 (mem_Icc.mp hj).1, (mem_Icc.mp hj).2⟩
    have hsubI : Icc (eqLo s0 jj p) (jj p) ⊆ Icc s0 (NR - 1) := fun j hj =>
      mem_Icc.mpr ⟨le_trans hl4 (mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; have := hjjle p hpP; omega⟩
    have hlo_mem : eqLo s0 jj p ∈ Icc (eqLo s0 jj p) (jj p + 1) := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hV' : ∀ m ∈ Icc (eqLo s0 jj p) (jj p + 1), Vp p ≤ CE * W m := by
      intro m hm
      have hm' := mem_Icc.mp hm
      have hWm := hWpos m (hsubW hm)
      rw [hVp]
      split_ifs with hp
      · exact mul_nonneg hCE0 hWm.le
      · have hjle : jj (p - 1) ≤ m := le_trans hl1 hm'.1
        exact hmono (jj (p - 1)) (hmemNR _ (hsite (p - 1) (by omega)).1 (by have := (hsite (p - 1) (by omega)).2; omega))
          m (hsubW hm) hjle
    have hS1p : ∀ j ∈ Icc (eqLo s0 jj p) (jj p), cm * ω ≤ |cas A (φ1 p) (φ2 p) j| := fun j hj =>
      hS1 p hmem j (mem_Icc.mpr ⟨le_trans hl1 (mem_Icc.mp hj).1, (mem_Icc.mp hj).2⟩)
    have he0' : ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k = 0 → e p k = 0 := by
      intro k hk hk0
      by_cases hp : p = 1
      · subst hp
        subst hk0
        exact he_seed 0 (mem_Icc.mpr ⟨le_rfl, hs0nn⟩)
      · have := hl5 hp
        have := (mem_Icc.mp hk).1
        omega
    have hLe' : ∀ k ∈ Icc (eqLo s0 jj p) (jj p), Lop A Q (e p) k = -(h * rt p k) := by
      intro k hk
      have hsol' : Lh h A Q ψ k = 0 := hsol k (hsubI hk)
      have hfun : e p = fun j => ψ j - (cvec φ1 φ2 jj p 0 * φ1 p j + cvec φ1 φ2 jj p 1 * φ2 p j) :=
        funext (fun j => by rw [he]; rfl)
      rw [hfun, hrt p k]
      exact residual_error h hh.ne' A Q ψ (φ1 p) (φ2 p) _ _ k hsol'
    have hrt' : ∀ k ∈ Icc (eqLo s0 jj p) (jj p), |rt p k| ≤ CrS * (ε * ρ k * W k * M k) := by
      intro k hk
      obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      have hk' := mem_Icc.mp hk
      have hkW : k ∈ Icc (eqLo s0 jj (n + 1)) (jj (n + 1) + 1) :=
        mem_Icc.mpr ⟨hk'.1, by omega⟩
      have hWk := hWpos k (hsubW hkW)
      have hMk := hMpos k (hsubW hkW)
      have hρk := hρ k
      have hc0 := (hcvb n (by omega)).1
      have hc1 := (hcvb n (by omega)).2
      have hc1z : n = 0 → cvec φ1 φ2 jj (n + 1) 1 = 0 := by
        intro hn
        subst hn
        simp [cvec_one]
      have hWak : n ≠ 0 → W (jj n) ≤ CE * W k := by
        intro hn
        have hlk : eqLo s0 jj (n + 1) = jj n + 1 := eqLo_succ s0 jj n (by omega)
        have hjk : jj n ≤ k := by omega
        exact hmono (jj n) (hmemNR _ (hsite n (by omega)).1 (by have := (hsite n (by omega)).2; omega))
          k (hsubW hkW) hjk
      have hk0 : n ≠ 0 → k ≠ 0 := by
        intro hn
        have hlk : eqLo s0 jj (n + 1) = jj n + 1 := eqLo_succ s0 jj n (by omega)
        have := hjjge n (by omega)
        omega
      have hu := hr1 (n + 1) (mem_Icc.mpr ⟨hp1, hpP⟩) k hk
      have hv : n ≠ 0 → |Lh h A Q (φ2 (n + 1)) k| ≤ ε * ρ k * (W k)⁻¹ * M k := fun hn =>
        hr2 (n + 1) (mem_Icc.mpr ⟨hp1, hpP⟩) k hk (hk0 hn)
      have hbd := rt_bound ε CE (Λ * (1 + CE ^ 2)) (cvec φ1 φ2 jj (n + 1) 0) (cvec φ1 φ2 jj (n + 1) 1)
        (Lh h A Q (φ1 (n + 1)) k) (Lh h A Q (φ2 (n + 1)) k) (W (jj n)) (W k) (M k) (ρ k) n hX1 hCE0 hε hρk
        hWk hMk.le (hWj n (by omega)) hWak hc0 (by simpa using hc1) hc1z hu hv
      rw [hrt]
      have hXP : (Λ * (1 + CE ^ 2)) ^ n ≤ (Λ * (1 + CE ^ 2)) ^ P :=
        pow_le_pow_right₀ hX1 (by omega)
      have hCpos : 0 ≤ (ε * ρ k * W k * M k) := by positivity
      calc _ ≤ (Λ * (1 + CE ^ 2)) ^ n * (1 + CE ^ 2) * (ε * ρ k * W k * M k) := hbd
        _ ≤ CrS * (ε * ρ k * W k * M k) := by
            apply mul_le_mul_of_nonneg_right _ hCpos
            rw [hCrS]
            unfold mvCrStar
            exact mul_le_mul_of_nonneg_right hXP (by positivity)
    have hbase : |e p (eqLo s0 jj p)| ≤ (1 + CE ^ 2) / cm * K * ap p * (W (eqLo s0 jj p) * M (eqLo s0 jj p)) := by
      by_cases hp : p = 1
      · subst hp
        rw [eqLo_one, he_seed s0 (mem_Icc.mpr ⟨hs0nn, le_rfl⟩), abs_zero]
        have := hMpos s0 (hmemNR _ hs0nn (by omega))
        have := hWpos s0 (hmemNR _ hs0nn (by omega))
        have hpos : 0 ≤ (1 + CE ^ 2) / cm * K * ap 1 * (W s0 * M s0) := by
          have := hap0 1
          have := hWpos s0 (hmemNR _ hs0nn (by omega))
          have := hMpos s0 (hmemNR _ hs0nn (by omega))
          positivity
        exact hpos
      · have hl' : eqLo s0 jj p - 1 = jj (p - 1) := by
          unfold eqLo
          rw [if_neg hp]
          ring
        have hsP : eqLo s0 jj p ∈ Icc (jj (p - 1)) (jj p + 1) := hsubA hlo_mem
        have hS1' : cm * ω ≤ |cas A (φ1 p) (φ2 p) (eqLo s0 jj p - 1)| := by
          rw [hl']
          exact hS1 p hmem _ (mem_Icc.mpr ⟨le_rfl, hjjle2 p hp1 hpP⟩)
        exact base_site ω cm CE K (ap p) (Vp p) A (eqLo s0 jj p) (e p) (φ1 p) (φ2 p) W M hω hcm hCE0 hK
          (hap0 p) (hVp0 p hp1 hpP) (hWpos _ (hsubW hlo_mem)) (hMpos _ (hsubW hlo_mem)).le hS1'
          (hφ1 p hmem _ hsP) (hφ2 p hmem _ hsP) (hV' _ hlo_mem) E2 E1
    have hsubS : ∀ j ∈ Icc (eqLo s0 jj p) (jj p), j ∈ Icc (eqLo s0 jj p) (jj p + 1) := fun j hj =>
      mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
    have hget := patch_volterra h ω cm CE K ε CrS (ap p) (Vp p) (Sp p) (th p)
      (2 * ((1 + CE ^ 2) / cm) * K * (ap p + K * CrS * th p)) A Q (eqLo s0 jj p) (jj p) (e p) (φ1 p) (φ2 p)
      (rt p) ρ M W hh hω hcm hCE0 hK hε hCrS0 (hap0 p) (hVp0 p hp1 hpP) hl2 (hSp p) (hth0 p) (hthω p)
      (hsmallth p hmem) rfl
      hS1p (fun j hj => hMpos j (hsubW hj)) (fun j hj => hWpos j (hsubW hj))
      (fun k hk j hj hkj => hmono k (hsubW hk) j (hsubW hj) hkj)
      (fun j hj => hφ1 p hmem j (hsubA hj)) (fun j hj => hφ2 p hmem j (hsubA hj)) hρ
      (fun k hk => hr1 p hmem k hk) (fun k hk hk0 => hr2 p hmem k hk hk0)
      hLe' hrt' he0' hV' E2 E1 hbase
    exact hget
  -- the entry claim, by induction over the patches
  have hE : ∀ p, 1 ≤ p → (p ≤ P →
      |cas A (e p) (φ2 p) (eqLo s0 jj p - 1)| ≤ ap p * ω ∧
      |cas A (e p) (φ1 p) (eqLo s0 jj p - 1)| ≤ ap p * ω * (Vp p) ^ 2) := by
    intro p hp1
    induction p, hp1 using Nat.le_induction with
    | base =>
      intro _
      have hz2 : cas A (e 1) (φ2 1) (eqLo s0 jj 1 - 1) = 0 := by
        rw [eqLo_one]
        exact cas_zero_entry A (e 1) (φ2 1) s0 hs0 hA (fun j hj0 hjs => he_seed j (mem_Icc.mpr ⟨hj0, hjs⟩))
      have hz1 : cas A (e 1) (φ1 1) (eqLo s0 jj 1 - 1) = 0 := by
        rw [eqLo_one]
        exact cas_zero_entry A (e 1) (φ1 1) s0 hs0 hA (fun j hj0 hjs => he_seed j (mem_Icc.mpr ⟨hj0, hjs⟩))
      have hV1 : Vp 1 = 0 := by rw [hVp]; simp
      rw [hz2, hz1, hV1, abs_zero]
      exact ⟨mul_nonneg (hap0 1) hω.le, by simp⟩
    | succ p hp ih =>
      intro hpP
      obtain ⟨E2p, E1p⟩ := ih (by omega)
      obtain ⟨_, hX2, hX1⟩ := hpatch p hp (by omega) E2p E1p
      obtain ⟨hdet, h00, h11, h01, h10⟩ := hT p hp (by omega)
      have hdet0 : (transMat φ1 φ2 jj p).det ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hdet
        have := inv_pos.mpr hΛ0
        linarith
      obtain ⟨b1, b2, b3, b4⟩ := bond_entries φ1 φ2 jj p hdet0
      have hsv0 : e p (jj p) = e (p + 1) (jj p) := by
        rw [he, he, psiHat_overlap φ1 φ2 jj p hp (jj p) b1 b2]
      have hsv1 : e p (jj p + 1) = e (p + 1) (jj p + 1) := by
        rw [he, he, psiHat_overlap φ1 φ2 jj p hp (jj p + 1) b3 b4]
      obtain ⟨r0, r1⟩ := cas_transfer_rel A (e p) (φ1 p) (φ2 p) (φ1 (p + 1)) (φ2 (p + 1)) (jj p)
        (transMat φ1 φ2 jj p 0 0) (transMat φ1 φ2 jj p 0 1) (transMat φ1 φ2 jj p 1 0)
        (transMat φ1 φ2 jj p 1 1) b1 b3 b2 b4
      have hdetf := Matrix.det_fin_two (transMat φ1 φ2 jj p)
      rw [hdetf] at hdet
      have hG0 : 0 ≤ ap p + K * CrS * th p :=
        add_nonneg (hap0 p) (mul_nonneg (mul_nonneg hK hCrS0) (hth0 p))
      obtain ⟨hF0, hF1⟩ := flux_transfer Λ CE (W (jj p)) ω (ap p + K * CrS * th p)
        (cas A (e p) (φ1 p) (jj p)) (cas A (e p) (φ2 p) (jj p))
        (cas A (e p) (φ1 (p + 1)) (jj p)) (cas A (e p) (φ2 (p + 1)) (jj p))
        (transMat φ1 φ2 jj p 0 0) (transMat φ1 φ2 jj p 0 1) (transMat φ1 φ2 jj p 1 0)
        (transMat φ1 φ2 jj p 1 1) hΛ0 hCE0 (hWj p (by omega)) hω.le hG0 hdet h00 h11 h01 h10 hX1 hX2 r0 r1
      have hκbound : κ * (ap p + K * CrS * th p) ≤ ap (p + 1) := by
        rw [hap p, hap (p + 1)]
        exact kappa_step κ (K * CrS) Y (th p) p hκ0 (mul_nonneg hK hCrS0) hY0 (hth0 p)
          (hthY p (mem_Icc.mpr ⟨hp, by omega⟩)) hp
      have hF1b : |cas A (e p) (φ2 (p + 1)) (jj p)| ≤ ap (p + 1) * ω := by
        refine le_trans hF1 ?_
        have e1 : 2 * Λ ^ 2 * (1 + CE ^ 2) * (ap p + K * CrS * th p) * ω
            = (κ * (ap p + K * CrS * th p)) * ω := by rw [hκe]
        rw [e1]
        exact mul_le_mul_of_nonneg_right hκbound hω.le
      have hF0b : |cas A (e p) (φ1 (p + 1)) (jj p)| ≤ ap (p + 1) * ω * (W (jj p)) ^ 2 := by
        refine le_trans hF0 ?_
        have e2 : 2 * Λ ^ 2 * (1 + CE ^ 2) * (ap p + K * CrS * th p) * ω * (W (jj p)) ^ 2
            = (κ * (ap p + K * CrS * th p)) * ω * (W (jj p)) ^ 2 := by rw [hκe]
        rw [e2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκbound hω.le) (sq_nonneg _)
      have hl : eqLo s0 jj (p + 1) - 1 = jj p := by
        rw [eqLo_succ s0 jj p hp]
        ring
      have hVp' : Vp (p + 1) = W (jj p) := by
        rw [hVp, if_neg (by omega), Nat.add_sub_cancel]
      rw [hl, hVp']
      constructor
      · rw [← cas_congr_e A (e p) (e (p + 1)) (φ2 (p + 1)) (jj p) hsv0 hsv1]
        exact hF1b
      · rw [← cas_congr_e A (e p) (e (p + 1)) (φ1 (p + 1)) (jj p) hsv0 hsv1]
        exact hF0b
  -- the bounds on the patch windows
  have hfinal : ∀ p, 1 ≤ p → p ≤ P → ∀ m ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |e p m| ≤ mvC cm CE K Λ P * (ε * Θ) * (W m * M m) := by
    intro p hp1 hpP m hm
    obtain ⟨E2, E1⟩ := hE p hp1 hpP
    obtain ⟨hint, _, _⟩ := hpatch p hp1 hpP E2 E1
    have hBq : 2 * ((1 + CE ^ 2) / cm) * K * (ap p + K * CrS * th p) ≤ mvC cm CE K Λ P * (ε * Θ) := by
      have hpow : (κ + 1) ^ p ≤ (κ + 1) ^ P := pow_le_pow_right₀ (by linarith) hpP
      have ha : ap p ≤ K * CrS * (κ + 1) ^ P * Y := by
        rw [hap p]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hCrS0)) hY0
      have hθ : K * CrS * th p ≤ K * CrS * Y :=
        mul_le_mul_of_nonneg_left (hthY p (mem_Icc.mpr ⟨hp1, hpP⟩)) (mul_nonneg hK hCrS0)
      have hsum : ap p + K * CrS * th p ≤ K * CrS * ((κ + 1) ^ P + 1) * Y := by
        have e3 : K * CrS * ((κ + 1) ^ P + 1) * Y = K * CrS * (κ + 1) ^ P * Y + K * CrS * Y := by ring
        linarith
      have hmC : mvC cm CE K Λ P * (ε * Θ)
          = 2 * ((1 + CE ^ 2) / cm) * K * (K * CrS * ((κ + 1) ^ P + 1)) * Y := by
        rw [← hY, mvC, ← hκ, ← hCrS]
      rw [hmC]
      have hc : 0 ≤ 2 * ((1 + CE ^ 2) / cm) * K := by positivity
      calc 2 * ((1 + CE ^ 2) / cm) * K * (ap p + K * CrS * th p)
          ≤ 2 * ((1 + CE ^ 2) / cm) * K * (K * CrS * ((κ + 1) ^ P + 1) * Y) :=
            mul_le_mul_of_nonneg_left hsum hc
        _ = 2 * ((1 + CE ^ 2) / cm) * K * (K * CrS * ((κ + 1) ^ P + 1)) * Y := by ring
    have hWM : 0 ≤ W m * M m := mul_nonneg (hWpos m (by
      have := mem_Icc.mp hm
      exact mem_Icc.mpr ⟨le_trans (by have := hlo p hp1 hpP; omega) this.1, by
        have := mem_Icc.mp hm; have := (hsite p hpP).2; omega⟩)).le (hMpos m (by
      have := mem_Icc.mp hm
      exact mem_Icc.mpr ⟨le_trans (by have := hlo p hp1 hpP; omega) this.1, by
        have := mem_Icc.mp hm; have := (hsite p hpP).2; omega⟩)).le
    calc |e p m| ≤ 2 * ((1 + CE ^ 2) / cm) * K * (ap p + K * CrS * th p) * (W m * M m) := hint m hm
      _ ≤ mvC cm CE K Λ P * (ε * Θ) * (W m * M m) := mul_le_mul_of_nonneg_right hBq hWM
  have hC0 : 0 ≤ mvC cm CE K Λ P := by
    unfold mvC mvCrStar mvKappa
    positivity
  have hbound1 : ∀ p, 1 ≤ p → p ≤ P → ∀ j ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |ψ j - psiHat φ1 φ2 jj p j| ≤ mvC cm CE K Λ P * (ε * Θ) * W j * M j := by
    intro p hp1 hpP j hj
    have := hfinal p hp1 hpP j hj
    rw [he] at this
    calc _ ≤ mvC cm CE K Λ P * (ε * Θ) * (W j * M j) := this
      _ = mvC cm CE K Λ P * (ε * Θ) * W j * M j := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro p hp j hj
    exact hbound1 p (mem_Icc.mp hp).1 (mem_Icc.mp hp).2 j hj
  · intro p hp1 hpP j hj
    have hdet0 : (transMat φ1 φ2 jj p).det ≠ 0 := by
      intro h0
      have := (hT p hp1 hpP).1
      rw [h0, abs_zero] at this
      have := inv_pos.mpr hΛ0
      linarith
    obtain ⟨b1, b2, b3, b4⟩ := bond_entries φ1 φ2 jj p hdet0
    have hj' := mem_Icc.mp hj
    have hcases : j = jj p ∨ j = jj p + 1 := by omega
    rcases hcases with rfl | rfl
    · exact psiHat_overlap φ1 φ2 jj p hp1 _ b1 b2
    · exact psiHat_overlap φ1 φ2 jj p hp1 _ b3 b4
  · intro j hj
    have hj' := mem_Icc.mp hj
    by_cases hjs : j < s0
    · refine ⟨1, mem_Icc.mpr ⟨le_rfl, hP⟩, ?_⟩
      have h0 := he_seed j (mem_Icc.mpr ⟨hj'.1, by omega⟩)
      rw [he 1 j] at h0
      rw [h0, abs_zero]
      have hW0 := hWpos j hj
      have hM0 := hMpos j hj
      have hC0' := hC0
      positivity
    · obtain ⟨p, hp1, hpP, hlo', hup⟩ := covering_patch s0 NR P jj hP hjj0 hjjP j (by omega) hj'.2
      exact ⟨p, mem_Icc.mpr ⟨hp1, hpP⟩, hbound1 p hp1 hpP j (mem_Icc.mpr ⟨hlo', hup⟩)⟩

/-! ### The transfer condition (S3) at a forbidden overlap -/

/-- Quotient step: `|n| ≤ 2 c P X` and `Dl P ≤ |D|` give `|n/D| ≤ (2c/Dl) X`. -/
lemma div_bound_aux (n D X c Dl P : ℝ) (hDl : 0 < Dl) (hP : 0 < P) (hD : Dl * P ≤ |D|)
    (hX : 0 ≤ X) (hc : 0 ≤ c) (hn : |n| ≤ 2 * c * P * X) : |n / D| ≤ (2 * c / Dl) * X := by
  have hDpos : 0 < |D| := lt_of_lt_of_le (mul_pos hDl hP) hD
  rw [abs_div, div_le_iff₀ hDpos]
  have h1 : (2 * c / Dl) * X * (Dl * P) ≤ (2 * c / Dl) * X * |D| :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have h2 : (2 * c / Dl) * X * (Dl * P) = 2 * c * P * X := by
    field_simp
  linarith

/-- The algebraic core of the forbidden-overlap transfer bound (`thm:eng-volterra`, remark after (S3), case (ii)):
entries of `U'⁻¹ U` for `2×2` matrices `U = (a_ij)`, `U' = (b_ij)` whose rows are at the sites `j, j+1` and whose
columns obey the envelope bounds with the weights `Wj, W1` (`Wj ≤ Cw W1`, `W1 ≤ Cw Wj`) and `|det U'| ≥ Dl Mj M1`. -/
lemma transfer_entries_bound (a11 a12 a21 a22 b11 b12 b21 b22 Wj W1 Mj M1 K Cw Dl : ℝ)
    (hWj : 0 < Wj) (hW1 : 0 < W1) (hMj : 0 < Mj) (hM1 : 0 < M1) (hK : 0 ≤ K) (hDl : 0 < Dl)
    (h1 : W1 ≤ Cw * Wj) (h2 : Wj ≤ Cw * W1)
    (ha11 : |a11| ≤ K * Wj * Mj) (ha12 : |a12| ≤ K * Wj⁻¹ * Mj)
    (ha21 : |a21| ≤ K * W1 * M1) (ha22 : |a22| ≤ K * W1⁻¹ * M1)
    (hb11 : |b11| ≤ K * Wj * Mj) (hb12 : |b12| ≤ K * Wj⁻¹ * Mj)
    (hb21 : |b21| ≤ K * W1 * M1) (hb22 : |b22| ≤ K * W1⁻¹ * M1)
    (hD : Dl * (Mj * M1) ≤ |b11 * b22 - b12 * b21|) :
    |(b22 * a11 - b12 * a21) / (b11 * b22 - b12 * b21)| ≤ 2 * K ^ 2 * Cw / Dl ∧
    |(b22 * a12 - b12 * a22) / (b11 * b22 - b12 * b21)| ≤ 2 * K ^ 2 * Cw / Dl * (Wj ^ 2)⁻¹ ∧
    |(b11 * a21 - b21 * a11) / (b11 * b22 - b12 * b21)| ≤ 2 * K ^ 2 * Cw / Dl * Wj ^ 2 ∧
    |(b11 * a22 - b21 * a12) / (b11 * b22 - b12 * b21)| ≤ 2 * K ^ 2 * Cw / Dl ∧
    |b11 * b22 - b12 * b21| ≤ 2 * K ^ 2 * Cw * (Mj * M1) := by
  have hCw : 0 < Cw := by
    by_contra hc
    have hc := not_lt.mp hc
    have : Cw * Wj ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hWj.le
    linarith
  have hr1 : W1 * Wj⁻¹ ≤ Cw := by
    rw [← div_eq_mul_inv, div_le_iff₀ hWj]; linarith
  have hr2 : Wj * W1⁻¹ ≤ Cw := by
    rw [← div_eq_mul_inv, div_le_iff₀ hW1]; linarith
  have hP : 0 < Mj * M1 := mul_pos hMj hM1
  have hWj2 : 0 < Wj ^ 2 := by positivity
  have hWj2i : 0 ≤ (Wj ^ 2)⁻¹ := by positivity
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  -- product bounds
  have bp : ∀ x y s t : ℝ, |x| ≤ s → |y| ≤ t → 0 ≤ s → |x * y| ≤ s * t := by
    intro x y s t hx hy hs
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hs
  -- Type A: weights cancel to Wj/W1 or W1/Wj
  have PA1 : |b22 * a11| ≤ K ^ 2 * (Mj * M1) * Cw := by
    have := bp _ _ _ _ hb22 ha11 (by positivity)
    have e : (K * W1⁻¹ * M1) * (K * Wj * Mj) = (K ^ 2 * (Mj * M1)) * (Wj * W1⁻¹) := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
  have PA2 : |b12 * a21| ≤ K ^ 2 * (Mj * M1) * Cw := by
    have := bp _ _ _ _ hb12 ha21 (by positivity)
    have e : (K * Wj⁻¹ * Mj) * (K * W1 * M1) = (K ^ 2 * (Mj * M1)) * (W1 * Wj⁻¹) := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
  have PA7 : |b21 * a12| ≤ K ^ 2 * (Mj * M1) * Cw := by
    have := bp _ _ _ _ hb21 ha12 (by positivity)
    have e : (K * W1 * M1) * (K * Wj⁻¹ * Mj) = (K ^ 2 * (Mj * M1)) * (W1 * Wj⁻¹) := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
  have PA8 : |b11 * a22| ≤ K ^ 2 * (Mj * M1) * Cw := by
    have := bp _ _ _ _ hb11 ha22 (by positivity)
    have e : (K * Wj * Mj) * (K * W1⁻¹ * M1) = (K ^ 2 * (Mj * M1)) * (Wj * W1⁻¹) := by ring
    rw [e] at this
    exact this.trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
  have PA3 : |b22 * a12| ≤ K ^ 2 * (Mj * M1) * Cw * (Wj ^ 2)⁻¹ := by
    have := bp _ _ _ _ hb22 ha12 (by positivity)
    have e : (K * W1⁻¹ * M1) * (K * Wj⁻¹ * Mj) = (K ^ 2 * (Mj * M1)) * (Wj * W1⁻¹) * (Wj ^ 2)⁻¹ := by
      field_simp
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by positivity)) hWj2i
  have PA4 : |b12 * a22| ≤ K ^ 2 * (Mj * M1) * Cw * (Wj ^ 2)⁻¹ := by
    have := bp _ _ _ _ hb12 ha22 (by positivity)
    have e : (K * Wj⁻¹ * Mj) * (K * W1⁻¹ * M1) = (K ^ 2 * (Mj * M1)) * (Wj * W1⁻¹) * (Wj ^ 2)⁻¹ := by
      field_simp
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by positivity)) hWj2i
  have PA5 : |b21 * a11| ≤ K ^ 2 * (Mj * M1) * Cw * Wj ^ 2 := by
    have := bp _ _ _ _ hb21 ha11 (by positivity)
    have e : (K * W1 * M1) * (K * Wj * Mj) = (K ^ 2 * (Mj * M1)) * (W1 * Wj⁻¹) * Wj ^ 2 := by
      field_simp
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 (by positivity)) hWj2.le
  have PA6 : |b11 * a21| ≤ K ^ 2 * (Mj * M1) * Cw * Wj ^ 2 := by
    have := bp _ _ _ _ hb11 ha21 (by positivity)
    have e : (K * Wj * Mj) * (K * W1 * M1) = (K ^ 2 * (Mj * M1)) * (W1 * Wj⁻¹) * Wj ^ 2 := by
      field_simp
    rw [e] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 (by positivity)) hWj2.le
  have hc : 0 ≤ K ^ 2 * Cw := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := div_bound_aux (b22 * a11 - b12 * a21) (b11 * b22 - b12 * b21) 1 (K ^ 2 * Cw) Dl (Mj * M1)
      hDl hP hD zero_le_one hc (by
        calc |b22 * a11 - b12 * a21| ≤ |b22 * a11| + |b12 * a21| := abs_sub _ _
          _ ≤ 2 * (K ^ 2 * Cw) * (Mj * M1) * 1 := by linarith)
    calc _ ≤ 2 * (K ^ 2 * Cw) / Dl * 1 := this
      _ = _ := by ring
  · have := div_bound_aux (b22 * a12 - b12 * a22) (b11 * b22 - b12 * b21) ((Wj ^ 2)⁻¹) (K ^ 2 * Cw) Dl (Mj * M1)
      hDl hP hD hWj2i hc (by
        calc |b22 * a12 - b12 * a22| ≤ |b22 * a12| + |b12 * a22| := abs_sub _ _
          _ ≤ 2 * (K ^ 2 * Cw) * (Mj * M1) * (Wj ^ 2)⁻¹ := by linarith)
    calc _ ≤ 2 * (K ^ 2 * Cw) / Dl * (Wj ^ 2)⁻¹ := this
      _ = _ := by ring
  · have := div_bound_aux (b11 * a21 - b21 * a11) (b11 * b22 - b12 * b21) (Wj ^ 2) (K ^ 2 * Cw) Dl (Mj * M1)
      hDl hP hD hWj2.le hc (by
        calc |b11 * a21 - b21 * a11| ≤ |b11 * a21| + |b21 * a11| := abs_sub _ _
          _ ≤ 2 * (K ^ 2 * Cw) * (Mj * M1) * Wj ^ 2 := by linarith)
    calc _ ≤ 2 * (K ^ 2 * Cw) / Dl * Wj ^ 2 := this
      _ = _ := by ring
  · have := div_bound_aux (b11 * a22 - b21 * a12) (b11 * b22 - b12 * b21) 1 (K ^ 2 * Cw) Dl (Mj * M1)
      hDl hP hD zero_le_one hc (by
        calc |b11 * a22 - b21 * a12| ≤ |b11 * a22| + |b21 * a12| := abs_sub _ _
          _ ≤ 2 * (K ^ 2 * Cw) * (Mj * M1) * 1 := by linarith)
    calc _ ≤ 2 * (K ^ 2 * Cw) / Dl * 1 := this
      _ = _ := by ring
  · have B1 : |b11 * b22| ≤ K ^ 2 * (Mj * M1) * Cw := by
      have := bp _ _ _ _ hb11 hb22 (by positivity)
      have e : (K * Wj * Mj) * (K * W1⁻¹ * M1) = (K ^ 2 * (Mj * M1)) * (Wj * W1⁻¹) := by ring
      rw [e] at this
      exact this.trans (mul_le_mul_of_nonneg_left hr2 (by positivity))
    have B2 : |b12 * b21| ≤ K ^ 2 * (Mj * M1) * Cw := by
      have := bp _ _ _ _ hb12 hb21 (by positivity)
      have e : (K * Wj⁻¹ * Mj) * (K * W1 * M1) = (K ^ 2 * (Mj * M1)) * (W1 * Wj⁻¹) := by ring
      rw [e] at this
      exact this.trans (mul_le_mul_of_nonneg_left hr1 (by positivity))
    calc |b11 * b22 - b12 * b21| ≤ |b11 * b22| + |b12 * b21| := abs_sub _ _
      _ ≤ 2 * K ^ 2 * Cw * (Mj * M1) := by linarith

lemma transMat_entries (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) :
    transMat φ1 φ2 jj p 0 0 = (φ2 (p+1) (jj p + 1) * φ1 p (jj p) - φ2 (p+1) (jj p) * φ1 p (jj p + 1))
        / (φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)) ∧
    transMat φ1 φ2 jj p 0 1 = (φ2 (p+1) (jj p + 1) * φ2 p (jj p) - φ2 (p+1) (jj p) * φ2 p (jj p + 1))
        / (φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)) ∧
    transMat φ1 φ2 jj p 1 0 = (φ1 (p+1) (jj p) * φ1 p (jj p + 1) - φ1 (p+1) (jj p + 1) * φ1 p (jj p))
        / (φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)) ∧
    transMat φ1 φ2 jj p 1 1 = (φ1 (p+1) (jj p) * φ2 p (jj p + 1) - φ1 (p+1) (jj p + 1) * φ2 p (jj p))
        / (φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)) ∧
    (transMat φ1 φ2 jj p).det
      = (φ1 p (jj p) * φ2 p (jj p + 1) - φ2 p (jj p) * φ1 p (jj p + 1))
        / (φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold transMat
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [bondMat, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Ring.inverse_eq_inv']
    ring
  · unfold transMat
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [bondMat, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Ring.inverse_eq_inv']
    ring
  · unfold transMat
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [bondMat, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Ring.inverse_eq_inv']
    ring
  · unfold transMat
    rw [Matrix.inv_def, Matrix.adjugate_fin_two]
    simp [bondMat, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Ring.inverse_eq_inv']
    ring
  · unfold transMat
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [bondMat, Matrix.det_fin_two_of]
    ring


/-- The Casoratian of a pair across the bond `j` is `-A_j det U`, `U` the matrix of the pair at the sites `j, j+1`. -/
lemma cas_eq_neg_det (A f g : ℤ → ℝ) (j : ℤ) :
    cas A f g j = -(A j * (f j * g (j + 1) - g j * f (j + 1))) := by
  unfold cas; ring

/-- **Forbidden-overlap transfer bound** (`thm:eng-volterra`, remark after (S3), case (ii)): at the overlap bond `j = j_p`
let both pairs satisfy the envelope bounds with the weights `W_j, W_{j+1}` (`W_{j+1} ≤ C_w W_j`; the opposite inequality is
the monotonicity), let both Casoratians be `≥ c₋ ω`, and let `A_j M_j M_{j+1} ≤ C_ω ω` (the paper's `𝒜_h(s_{j_p}) 𝖬 𝖬 ≍ ω_*`).
Then the transfer matrix `M_p = transMat p` satisfies (S3) with `Λ = max 1 (2K²C_w C_ω/c₋)`. -/
theorem transfer_of_forbidden_overlap (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ) (p : ℕ) (A W M : ℤ → ℝ)
    (ω cm K Cw Cω : ℝ) (hA : 0 < A (jj p)) (hω : 0 < ω) (hcm : 0 < cm) (hK : 0 ≤ K)
    (hWj : 0 < W (jj p)) (hW1 : 0 < W (jj p + 1)) (hMj : 0 < M (jj p)) (hM1 : 0 < M (jj p + 1))
    (hw1 : W (jj p + 1) ≤ Cw * W (jj p)) (hw2 : W (jj p) ≤ Cw * W (jj p + 1))
    (hAM : A (jj p) * (M (jj p) * M (jj p + 1)) ≤ Cω * ω)
    (hq : ∀ q, q = p ∨ q = p + 1 →
      |φ1 q (jj p)| ≤ K * W (jj p) * M (jj p) ∧ |φ2 q (jj p)| ≤ K * (W (jj p))⁻¹ * M (jj p) ∧
      |φ1 q (jj p + 1)| ≤ K * W (jj p + 1) * M (jj p + 1) ∧
      |φ2 q (jj p + 1)| ≤ K * (W (jj p + 1))⁻¹ * M (jj p + 1))
    (hc : ∀ q, q = p ∨ q = p + 1 → cm * ω ≤ |cas A (φ1 q) (φ2 q) (jj p)|) :
    (max 1 (2 * K ^ 2 * Cw * Cω / cm))⁻¹ ≤ |(transMat φ1 φ2 jj p).det| ∧
    |transMat φ1 φ2 jj p 0 0| ≤ max 1 (2 * K ^ 2 * Cw * Cω / cm) ∧
    |transMat φ1 φ2 jj p 1 1| ≤ max 1 (2 * K ^ 2 * Cw * Cω / cm) ∧
    |transMat φ1 φ2 jj p 0 1| ≤ max 1 (2 * K ^ 2 * Cw * Cω / cm) * (W (jj p) ^ 2)⁻¹ ∧
    |transMat φ1 φ2 jj p 1 0| ≤ max 1 (2 * K ^ 2 * Cw * Cω / cm) * W (jj p) ^ 2 := by
  set Wj := W (jj p) with hWjdef
  set W1 := W (jj p + 1) with hW1def
  set Mj := M (jj p) with hMjdef
  set M1 := M (jj p + 1) with hM1def
  have hP : 0 < Mj * M1 := mul_pos hMj hM1
  have hCω : 0 < Cω := by
    have h0 : 0 < A (jj p) * (Mj * M1) := mul_pos hA hP
    by_contra hneg
    have hneg := not_lt.mp hneg
    have : Cω * ω ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hω.le
    linarith
  have hDl : 0 < cm / Cω := div_pos hcm hCω
  -- determinant lower bound for the pair of the patch `q`
  have hdet : ∀ q, q = p ∨ q = p + 1 →
      (cm / Cω) * (Mj * M1) ≤ |φ1 q (jj p) * φ2 q (jj p + 1) - φ2 q (jj p) * φ1 q (jj p + 1)| := by
    intro q hq'
    have h1 := hc q hq'
    rw [cas_eq_neg_det, abs_neg, abs_mul, abs_of_pos hA] at h1
    -- A |det| ≥ cm ω ≥ cm A Mj M1 / Cω
    have h2 : cm * ω * Cω ≥ cm * (A (jj p) * (Mj * M1)) := by
      have := mul_le_mul_of_nonneg_left hAM hcm.le
      nlinarith
    have h3 : cm * (A (jj p) * (Mj * M1)) ≤ A (jj p) * |φ1 q (jj p) * φ2 q (jj p + 1) - φ2 q (jj p) * φ1 q (jj p + 1)| * Cω := by
      have := mul_le_mul_of_nonneg_right h1 hCω.le
      nlinarith
    have h4 : cm / Cω * (Mj * M1) * (A (jj p) * Cω) ≤
        |φ1 q (jj p) * φ2 q (jj p + 1) - φ2 q (jj p) * φ1 q (jj p + 1)| * (A (jj p) * Cω) := by
      have e : cm / Cω * (Mj * M1) * (A (jj p) * Cω) = cm * (A (jj p) * (Mj * M1)) := by
        field_simp
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right h4 (mul_pos hA hCω)
  obtain ⟨b1, b2, b3, b4⟩ := hq (p + 1) (Or.inr rfl)
  obtain ⟨a1, a2, a3, a4⟩ := hq p (Or.inl rfl)
  have hDb := hdet (p + 1) (Or.inr rfl)
  have hDa := hdet p (Or.inl rfl)
  obtain ⟨e00, e01, e10, e11, edet⟩ := transMat_entries φ1 φ2 jj p
  obtain ⟨t00, t01, t10, t11, tD⟩ := transfer_entries_bound (φ1 p (jj p)) (φ2 p (jj p)) (φ1 p (jj p + 1))
    (φ2 p (jj p + 1)) (φ1 (p+1) (jj p)) (φ2 (p+1) (jj p)) (φ1 (p+1) (jj p + 1)) (φ2 (p+1) (jj p + 1))
    Wj W1 Mj M1 K Cw (cm / Cω) hWj hW1 hMj hM1 hK hDl hw1 hw2 a1 a2 a3 a4 b1 b2 b3 b4 hDb
  have hLam : 2 * K ^ 2 * Cw / (cm / Cω) = 2 * K ^ 2 * Cw * Cω / cm := by
    field_simp
  rw [hLam] at t00 t01 t10 t11
  set Λe := 2 * K ^ 2 * Cw * Cω / cm with hΛe
  have hle : Λe ≤ max 1 Λe := le_max_right _ _
  have hΛpos : 0 < max 1 Λe := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the determinant of the transfer matrix
    rw [edet, abs_div]
    set Dd := |φ1 (p+1) (jj p) * φ2 (p+1) (jj p + 1) - φ2 (p+1) (jj p) * φ1 (p+1) (jj p + 1)| with hDd
    have hDdpos : 0 < Dd := lt_of_lt_of_le (mul_pos hDl hP) hDb
    rw [le_div_iff₀ hDdpos]
    have hT : 2 * K ^ 2 * Cw * (Mj * M1) = Λe * (cm / Cω) * (Mj * M1) := by
      rw [hΛe]; field_simp
    have h1 : (max 1 Λe)⁻¹ * Dd ≤ (max 1 Λe)⁻¹ * (Λe * (cm / Cω) * (Mj * M1)) :=
      mul_le_mul_of_nonneg_left (tD.trans_eq hT) (inv_nonneg.mpr hΛpos.le)
    have h2 : (max 1 Λe)⁻¹ * Λe ≤ 1 := by
      rw [inv_mul_le_iff₀ hΛpos]; linarith
    have h3 : (max 1 Λe)⁻¹ * (Λe * (cm / Cω) * (Mj * M1)) ≤ (cm / Cω) * (Mj * M1) := by
      have : (max 1 Λe)⁻¹ * (Λe * (cm / Cω) * (Mj * M1)) = ((max 1 Λe)⁻¹ * Λe) * ((cm / Cω) * (Mj * M1)) := by ring
      rw [this]
      calc _ ≤ 1 * ((cm / Cω) * (Mj * M1)) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := one_mul _
    linarith
  · rw [e00]; exact t00.trans hle
  · rw [e11]; exact t11.trans hle
  · rw [e01]; exact t01.trans (mul_le_mul_of_nonneg_right hle (by positivity))
  · rw [e10]; exact t10.trans (mul_le_mul_of_nonneg_right hle (by positivity))


/-- Multi-patch stability with the forbidden-overlap transfer condition derived (`thm:eng-volterra`(a) with (S3) replaced
by the paper's case (ii), "forbidden overlap").  Instead of the transfer bounds (S3) it assumes, at each overlap bond
`j_p`: `A_{j_p} > 0`, `W_{j_p+1} ≤ C_w W_{j_p}` (no jump of the weight; the opposite inequality is the monotonicity) and
`A_{j_p} M_{j_p} M_{j_p+1} ≤ C_ω ω` (the paper's `𝒜_h(s_{j_p}) 𝖬 𝖬 ≍ ω_*`); (S3) then holds with
`Λ = max 1 (2K² max(C_w,C_E) C_ω/c₋)` (`transfer_of_forbidden_overlap`).  The conclusions are those of `volterra_multi`. -/
theorem volterra_multi_forbidden (h ω cm CE K ε Cw Cω : ℝ) (A Q ψ ρ M W : ℤ → ℝ) (s0 NR : ℤ) (P : ℕ)
    (jj : ℕ → ℤ) (φ1 φ2 : ℕ → ℤ → ℝ)
    (hh : 0 < h) (hω : 0 < ω) (hcm : 0 < cm) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hP : 1 ≤ P) (hjj0 : jj 0 = 0) (hjjmono : ∀ p < P, jj p < jj (p + 1)) (hjjP : jj P = NR - 1)
    (hs0 : s0 = 0 ∨ s0 = 1) (hA : s0 = 0 → A (-1) = 0)
    (hS1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p), cm * ω ≤ |cas A (φ1 p) (φ2 p) j|)
    (hMpos : ∀ j ∈ Icc 0 NR, 0 < M j) (hWpos : ∀ j ∈ Icc 0 NR, 0 < W j)
    (hmono : ∀ k ∈ Icc 0 NR, ∀ j ∈ Icc 0 NR, k ≤ j → W k ≤ CE * W j)
    (hφ1 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1), |φ1 p j| ≤ K * W j * M j)
    (hφ2 : ∀ p ∈ Icc 1 P, ∀ j ∈ Icc (jj (p - 1)) (jj p + 1), |φ2 p j| ≤ K * (W j)⁻¹ * M j)
    (hρ : ∀ k, 0 ≤ ρ k)
    (hr1 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), |Lh h A Q (φ1 p) k| ≤ ε * ρ k * W k * M k)
    (hr2 : ∀ p ∈ Icc 1 P, ∀ k ∈ Icc (eqLo s0 jj p) (jj p), k ≠ 0 →
      |Lh h A Q (φ2 p) k| ≤ ε * ρ k * (W k)⁻¹ * M k)
    (hover : ∀ p, 1 ≤ p → p < P → 0 < A (jj p) ∧ W (jj p + 1) ≤ Cw * W (jj p) ∧
      A (jj p) * (M (jj p) * M (jj p + 1)) ≤ Cω * ω)
    (hsol : ∀ k ∈ Icc s0 (NR - 1), Lh h A Q ψ k = 0)
    (hseed : ∀ j ∈ Icc 0 s0, ψ j = φ1 1 j)
    (hsmall : ε * volTheta h ω s0 jj P ρ M ≤ mvCstar cm CE K) :
    (∀ p ∈ Icc 1 P, ∀ j ∈ Icc (eqLo s0 jj p) (jj p + 1),
      |ψ j - psiHat φ1 φ2 jj p j|
        ≤ mvC cm CE K (max 1 (2 * K ^ 2 * max Cw CE * Cω / cm)) P * (ε * volTheta h ω s0 jj P ρ M) * W j * M j) ∧
    (∀ p, 1 ≤ p → p < P → ∀ j ∈ Icc (jj p) (jj p + 1),
      psiHat φ1 φ2 jj p j = psiHat φ1 φ2 jj (p + 1) j) ∧
    (∀ j ∈ Icc 0 NR, ∃ p ∈ Icc 1 P,
      |ψ j - psiHat φ1 φ2 jj p j|
        ≤ mvC cm CE K (max 1 (2 * K ^ 2 * max Cw CE * Cω / cm)) P * (ε * volTheta h ω s0 jj P ρ M) * W j * M j) := by
  have hjjge : ∀ p, p ≤ P → 0 ≤ jj p := fun p hp => by
    have := jj_mono_le jj P hjjmono 0 p (Nat.zero_le _) hp
    rw [hjj0] at this
    exact this
  have hjjle : ∀ p, p ≤ P → jj p ≤ NR - 1 := fun p hp => by
    have := jj_mono_le jj P hjjmono p P hp le_rfl
    rw [hjjP] at this
    exact this
  have hT : ∀ p, 1 ≤ p → p < P →
      (max 1 (2 * K ^ 2 * max Cw CE * Cω / cm))⁻¹ ≤ |(transMat φ1 φ2 jj p).det| ∧
      |transMat φ1 φ2 jj p 0 0| ≤ max 1 (2 * K ^ 2 * max Cw CE * Cω / cm) ∧
      |transMat φ1 φ2 jj p 1 1| ≤ max 1 (2 * K ^ 2 * max Cw CE * Cω / cm) ∧
      |transMat φ1 φ2 jj p 0 1| ≤ max 1 (2 * K ^ 2 * max Cw CE * Cω / cm) * (W (jj p) ^ 2)⁻¹ ∧
      |transMat φ1 φ2 jj p 1 0| ≤ max 1 (2 * K ^ 2 * max Cw CE * Cω / cm) * W (jj p) ^ 2 := by
    intro p hp1 hpP
    obtain ⟨hAp, hw, hAM⟩ := hover p hp1 hpP
    have hj0 := hjjge p hpP.le
    have hj1 : jj p + 1 ≤ NR := by have := hjjle p hpP.le; omega
    have hjm : jj p < jj (p + 1) := hjjmono p hpP
    have hjm' : jj (p - 1) ≤ jj p := jj_mono_le jj P hjjmono (p - 1) p (by omega) hpP.le
    have hmemj : jj p ∈ Icc 0 NR := mem_Icc.mpr ⟨hj0, by omega⟩
    have hmemj1 : jj p + 1 ∈ Icc 0 NR := mem_Icc.mpr ⟨by omega, hj1⟩
    have hWj := hWpos _ hmemj
    have hW1 := hWpos _ hmemj1
    have hw1 : W (jj p + 1) ≤ max Cw CE * W (jj p) :=
      hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWj.le)
    have hw2 : W (jj p) ≤ max Cw CE * W (jj p + 1) :=
      (hmono _ hmemj _ hmemj1 (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW1.le)
    have hpP' : p ∈ Icc 1 P := mem_Icc.mpr ⟨hp1, hpP.le⟩
    have hp1P : p + 1 ∈ Icc 1 P := mem_Icc.mpr ⟨by omega, hpP⟩
    refine transfer_of_forbidden_overlap φ1 φ2 jj p A W M ω cm K (max Cw CE) Cω hAp hω hcm hK hWj hW1
      (hMpos _ hmemj) (hMpos _ hmemj1) hw1 hw2 hAM ?_ ?_
    · intro q hq
      rcases hq with rfl | rfl
      · refine ⟨hφ1 q hpP' _ (mem_Icc.mpr ⟨hjm', by omega⟩), hφ2 q hpP' _ (mem_Icc.mpr ⟨hjm', by omega⟩),
          hφ1 q hpP' _ (mem_Icc.mpr ⟨by omega, le_rfl⟩), hφ2 q hpP' _ (mem_Icc.mpr ⟨by omega, le_rfl⟩)⟩
      · have e : (p + 1 - 1) = p := by omega
        refine ⟨hφ1 (p + 1) hp1P _ (mem_Icc.mpr ⟨by rw [e], by omega⟩),
          hφ2 (p + 1) hp1P _ (mem_Icc.mpr ⟨by rw [e], by omega⟩),
          hφ1 (p + 1) hp1P _ (mem_Icc.mpr ⟨by rw [e]; omega, by omega⟩),
          hφ2 (p + 1) hp1P _ (mem_Icc.mpr ⟨by rw [e]; omega, by omega⟩)⟩
    · intro q hq
      rcases hq with rfl | rfl
      · exact hS1 q hpP' _ (mem_Icc.mpr ⟨hjm', le_rfl⟩)
      · have e : (p + 1 - 1) = p := by omega
        exact hS1 (p + 1) hp1P _ (mem_Icc.mpr ⟨by rw [e], hjm.le⟩)
  exact volterra_multi h ω cm CE K ε (max 1 (2 * K ^ 2 * max Cw CE * Cω / cm)) A Q ψ ρ M W s0 NR P jj φ1 φ2
    hh hω hcm hK hε (le_max_left _ _) hP hjj0 hjjmono hjjP hs0 hA hS1 hMpos hWpos hmono hφ1 hφ2 hρ hr1 hr2 hT
    hsol hseed hsmall

/-! ### Non-vacuity: two patches, the two-node seed, the exact pair `cos(iθ)`, `sin(iθ)` -/

/-- Non-vacuity of `volterra_multi`: two patches (`P = 2`, breakpoints `j_p = p`, `N_R = 3`, windows `[0,2]`, `[1,3]`,
equation sites `[1,2]`), the two-node seed (`s₀ = 1`), `A = 1`, `Q = 2cos θ`, the exact pair `φ¹ = cos(iθ)`,
`φ² = sin(iθ)` on both patches (so `M_p = I`, `c_p = (1,0)`), `ε = 0`, `ψ = φ¹`.  Every hypothesis of
`volterra_multi` holds (`sin θ ≠ 0`), and its conclusion is the vanishing error `ψ_j = ψ̂_{p,j}` on the windows. -/
theorem volterra_multi_instance (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    ∀ p ∈ Icc 1 2, ∀ j ∈ Icc (eqLo 1 (fun n : ℕ => (n : ℤ)) p) ((p : ℤ) + 1),
      |(fun i : ℤ => Real.cos (i * θ)) j
        - psiHat (fun _ i => Real.cos (i * θ)) (fun _ i => Real.sin (i * θ)) (fun n : ℕ => (n : ℤ)) p j| ≤ 0 := by
  have hω : 0 < |Real.sin θ| := abs_pos.mpr hθ
  have hdetB : (bondMat (fun _ i => Real.cos (i * θ)) (fun _ i => Real.sin (i * θ)) 1 ((1 : ℕ) : ℤ)).det
      = Real.sin θ := by
    unfold bondMat
    rw [Matrix.det_fin_two_of]
    have e := Real.sin_sub (2 * θ) θ
    rw [show 2 * θ - θ = θ by ring] at e
    push_cast
    norm_num
    linear_combination (-1 : ℝ) * e
  have hT1 : transMat (fun _ i => Real.cos (i * θ)) (fun _ i => Real.sin (i * θ)) (fun n : ℕ => (n : ℤ)) 1 = 1 := by
    unfold transMat
    have hU : (bondMat (fun _ i => Real.cos (i * θ)) (fun _ i => Real.sin (i * θ)) (1 + 1)
        (((1 : ℕ) : ℤ))).det ≠ 0 := by
      show (bondMat (fun _ i => Real.cos (i * θ)) (fun _ i => Real.sin (i * θ)) 1 ((1 : ℕ) : ℤ)).det ≠ 0
      rw [hdetB]
      exact hθ
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU)
  have key := volterra_multi (h := 1) (ω := |Real.sin θ|) (cm := 1) (CE := 1) (K := 1) (ε := 0) (Λ := 1)
    (A := fun _ => 1) (Q := fun _ => 2 * Real.cos θ) (ψ := fun i : ℤ => Real.cos (i * θ))
    (ρ := fun _ => 1) (M := fun _ => 1) (W := fun _ => 1) (s0 := 1) (NR := 3) (P := 2)
    (jj := fun n : ℕ => (n : ℤ)) (φ1 := fun _ i => Real.cos (i * θ)) (φ2 := fun _ i => Real.sin (i * θ))
    (hh := one_pos) (hω := hω) (hcm := one_pos) (hK := zero_le_one) (hε := le_rfl) (hΛ := le_rfl)
    (hP := by norm_num) (hjj0 := rfl) (hjjmono := fun p _ => by simp) (hjjP := by norm_num)
    (hs0 := Or.inr rfl) (hA := fun h0 => absurd h0 (by norm_num))
    (hS1 := fun p _ j _ => by
      show 1 * |Real.sin θ| ≤ |cas (fun _ => (1 : ℝ)) (fun i : ℤ => Real.cos (i * θ))
        (fun i : ℤ => Real.sin (i * θ)) j|
      rw [(cos_sin_solutions θ).2.2 j, one_mul, abs_neg])
    (hMpos := fun j _ => one_pos) (hWpos := fun j _ => one_pos)
    (hmono := fun k _ j _ _ => by norm_num)
    (hφ1 := fun p _ j _ => by
      show |Real.cos (j * θ)| ≤ 1 * 1 * 1
      rw [mul_one, mul_one]
      exact Real.abs_cos_le_one _)
    (hφ2 := fun p _ j _ => by
      show |Real.sin (j * θ)| ≤ 1 * (1 : ℝ)⁻¹ * 1
      rw [inv_one, mul_one, mul_one]
      exact Real.abs_sin_le_one _)
    (hρ := fun _ => zero_le_one)
    (hr1 := fun p _ k _ => by
      have hz : Lop (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ)) k = 0 :=
        (cos_sin_solutions θ).1 k
      show |Lh 1 (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ)) k|
        ≤ 0 * 1 * 1 * 1
      simp [Lh, hz])
    (hr2 := fun p _ k _ _ => by
      have hz : Lop (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.sin (i * θ)) k = 0 :=
        (cos_sin_solutions θ).2.1 k
      show |Lh 1 (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.sin (i * θ)) k|
        ≤ 0 * 1 * (1 : ℝ)⁻¹ * 1
      simp [Lh, hz])
    (hT := fun p hp1 hp2 => by
      have hp : p = 1 := by omega
      subst hp
      rw [hT1, Matrix.det_one]
      simp)
    (hsol := fun k _ => by
      show Lh 1 (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ)) k = 0
      simp [Lh, (cos_sin_solutions θ).1 k])
    (hseed := fun j _ => rfl)
    (hsmall := by
      rw [zero_mul]
      unfold mvCstar
      positivity)
  intro p hp j hj
  have h1 := key.1 p hp j hj
  simpa using h1


/-! ### Perturbed instances (`ε > 0`, `ψ ≠ ψ̂`), two-node and hard-edge seeds -/

lemma mvC_inst : mvC 1 1 1 1 2 = 832 := by
  norm_num [mvC, mvCrStar, mvKappa]

lemma mvCstar_inst : mvCstar 1 1 1 = 1 / 5 := by
  norm_num [mvCstar]

lemma volTheta_two_node (h ω : ℝ) :
    volTheta h ω 1 (fun n : ℕ => (n : ℤ)) 2 (fun _ => 1) (fun _ => 1) = h / ω * 2 := by
  have e1 : eqLo 1 (fun n : ℕ => (n : ℤ)) 1 = 1 := eqLo_one _ _
  have e2 : eqLo 1 (fun n : ℕ => (n : ℤ)) 2 = 2 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, eqLo_succ _ _ 1 le_rfl]; simp
  unfold volTheta
  have : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [this, Finset.sum_pair (by norm_num), e1, e2]
  norm_num

lemma volTheta_hard_edge (h ω : ℝ) :
    volTheta h ω 0 (fun n : ℕ => (n : ℤ)) 2 (fun _ => 1) (fun _ => 1) = h / ω * 3 := by
  have e1 : eqLo 0 (fun n : ℕ => (n : ℤ)) 1 = 0 := eqLo_one _ _
  have e2 : eqLo 0 (fun n : ℕ => (n : ℤ)) 2 = 2 := by
    rw [show (2:ℕ) = 1 + 1 from rfl, eqLo_succ _ _ 1 le_rfl]; simp
  unfold volTheta
  have : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [this, Finset.sum_pair (by norm_num), e1, e2]
  norm_num [Finset.sum_const, Int.card_Icc]


/-- If the transfer matrix `M_1` is the identity, then `ψ̂_p = φ¹_p` on the two patches (`c_1 = c_2 = (1,0)`). -/
lemma psiHat_eq_phi1_of_trans_one (φ1 φ2 : ℕ → ℤ → ℝ) (jj : ℕ → ℤ)
    (hT : transMat φ1 φ2 jj 1 = 1) (p : ℕ) (hp : p = 1 ∨ p = 2) (j : ℤ) :
    psiHat φ1 φ2 jj p j = φ1 p j := by
  rcases hp with rfl | rfl
  · unfold psiHat
    rw [cvec_one]
    simp
  · unfold psiHat
    have hc : cvec φ1 φ2 jj 2 = mulMV (transMat φ1 φ2 jj 1) (cvec φ1 φ2 jj 1) := cvec_succ_succ φ1 φ2 jj 0
    rw [hc, hT, cvec_one]
    simp [mulMV]

/-- The trigonometric pair has the identity transfer matrix `M_1` (same pair on both patches). -/
lemma transMat_trig_one (θ' : ℝ) (hθ' : Real.sin θ' ≠ 0) :
    transMat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ')) (fun n : ℕ => (n : ℤ)) 1 = 1 := by
  have hdetB : (bondMat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ')) 1 ((1 : ℕ) : ℤ)).det
      = Real.sin θ' := by
    unfold bondMat
    rw [Matrix.det_fin_two_of]
    have e := Real.sin_sub (2 * θ') θ'
    rw [show 2 * θ' - θ' = θ' by ring] at e
    push_cast
    norm_num
    linear_combination (-1 : ℝ) * e
  unfold transMat
  have hU : (bondMat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ')) (1 + 1)
      (((1 : ℕ) : ℤ))).det ≠ 0 := by
    show (bondMat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ')) 1 ((1 : ℕ) : ℤ)).det ≠ 0
    rw [hdetB]
    exact hθ'
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU)

/-- **Perturbed multi-patch instance, two-node seed** (`ε > 0`, `ψ ≠ ψ̂`).  Two patches (`j_p = p`, `N_R = 3`), `A = 1`,
`Q = 2cosθ`, the pair `φ¹ = cos(iθ')`, `φ² = sin(iθ')` on both patches (`M_1 = I`, `ψ̂_p = φ¹`), the exact solution
`ψ = pertSol θ θ'` with the seed `ψ_0 = φ¹_0`, `ψ_1 = φ¹_1`, and the residual size
`ε = |2cosθ'-2cosθ|/h > 0`.  Here `εΘ = 2|2cosθ'-2cosθ|/|sinθ'|` is independent of `h`; the smallness `εΘ ≤ c* = 1/5` is the
hypothesis `hsmall` (satisfiable, see `volterra_multi_perturbed_params`).  The conclusion is the bound of
`volterra_multi` with the explicit constant `C = 832`, together with the non-vanishing of the error at some site. -/
theorem volterra_multi_instance_perturbed (h θ θ' : ℝ) (hh : 0 < h) (hθ : Real.sin θ ≠ 0)
    (hθ' : Real.sin θ' ≠ 0) (hne : Real.cos θ ≠ Real.cos θ')
    (hsmall : 2 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|) ≤ 1 / 5) :
    0 < |2 * Real.cos θ' - 2 * Real.cos θ| / h ∧
    (∀ p ∈ Icc 1 2, ∀ j ∈ Icc (eqLo 1 (fun n : ℕ => (n : ℤ)) p) ((p : ℤ) + 1),
      |pertSol θ θ' j - psiHat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ'))
          (fun n : ℕ => (n : ℤ)) p j|
        ≤ 832 * (2 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|))) ∧
    (∃ p ∈ Icc 1 2, ∃ j ∈ Icc (eqLo 1 (fun n : ℕ => (n : ℤ)) p) ((p : ℤ) + 1),
      pertSol θ θ' j ≠ psiHat (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ'))
          (fun n : ℕ => (n : ℤ)) p j) := by
  have hω : 0 < |Real.sin θ'| := abs_pos.mpr hθ'
  have hT1 := transMat_trig_one θ' hθ'
  have hεpos : 0 < |2 * Real.cos θ' - 2 * Real.cos θ| / h :=
    div_pos (abs_pos.mpr (by intro h'; apply hne; linarith)) hh
  have hεΘ : |2 * Real.cos θ' - 2 * Real.cos θ| / h * (h / |Real.sin θ'| * 2)
      = 2 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|) := by
    field_simp
  have key := volterra_multi (h := h) (ω := |Real.sin θ'|) (cm := 1) (CE := 1) (K := 1)
    (ε := |2 * Real.cos θ' - 2 * Real.cos θ| / h) (Λ := 1)
    (A := fun _ => 1) (Q := fun _ => 2 * Real.cos θ) (ψ := pertSol θ θ')
    (ρ := fun _ => 1) (M := fun _ => 1) (W := fun _ => 1) (s0 := 1) (NR := 3) (P := 2)
    (jj := fun n : ℕ => (n : ℤ)) (φ1 := fun _ i => Real.cos (i * θ')) (φ2 := fun _ i => Real.sin (i * θ'))
    (hh := hh) (hω := hω) (hcm := one_pos) (hK := zero_le_one) (hε := hεpos.le) (hΛ := le_rfl)
    (hP := by norm_num) (hjj0 := rfl) (hjjmono := fun p _ => by simp) (hjjP := by norm_num)
    (hs0 := Or.inr rfl) (hA := fun h0 => absurd h0 (by norm_num))
    (hS1 := fun p _ j _ => by
      show 1 * |Real.sin θ'| ≤ |cas (fun _ => (1 : ℝ)) (fun i : ℤ => Real.cos (i * θ'))
        (fun i : ℤ => Real.sin (i * θ')) j|
      rw [(cos_sin_solutions θ').2.2 j, one_mul, abs_neg])
    (hMpos := fun j _ => one_pos) (hWpos := fun j _ => one_pos)
    (hmono := fun k _ j _ _ => by norm_num)
    (hφ1 := fun p _ j _ => by
      show |Real.cos (j * θ')| ≤ 1 * 1 * 1
      rw [mul_one, mul_one]
      exact Real.abs_cos_le_one _)
    (hφ2 := fun p _ j _ => by
      show |Real.sin (j * θ')| ≤ 1 * (1 : ℝ)⁻¹ * 1
      rw [inv_one, mul_one, mul_one]
      exact Real.abs_sin_le_one _)
    (hρ := fun _ => zero_le_one)
    (hr1 := fun p _ k _ => by
      show |Lh h (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.cos (i * θ')) k|
        ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h * 1 * 1 * 1
      simpa only [mul_one] using abs_Lh_cos_pert h θ θ' hh k)
    (hr2 := fun p _ k _ _ => by
      show |Lh h (fun _ => (1 : ℝ)) (fun _ => 2 * Real.cos θ) (fun i : ℤ => Real.sin (i * θ')) k|
        ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h * 1 * (1 : ℝ)⁻¹ * 1
      simpa only [mul_one, inv_one] using abs_Lh_sin_pert h θ θ' hh k)
    (hT := fun p hp1 hp2 => by
      have hp : p = 1 := by omega
      subst hp
      rw [hT1, Matrix.det_one]
      simp)
    (hsol := fun k _ => Lh_pertSol h θ θ' k)
    (hseed := fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · simp [pertSol]
      · rw [pertSol_one θ θ' hθ]; simp)
    (hsmall := by
      rw [volTheta_two_node, hεΘ, mvCstar_inst]
      exact hsmall)
  have hψ := psiHat_eq_phi1_of_trans_one (fun _ i => Real.cos (i * θ')) (fun _ i => Real.sin (i * θ'))
    (fun n : ℕ => (n : ℤ)) hT1
  refine ⟨hεpos, ?_, ?_⟩
  · intro p hp j hj
    have hb := key.1 p hp j hj
    rw [volTheta_two_node, hεΘ, mvC_inst] at hb
    simpa using hb
  · rcases pertSol_ne_of_cos_ne θ θ' hθ hne with h2 | h3
    · refine ⟨1, by simp, 2, ?_, ?_⟩
      · simp [eqLo_one]
      · rw [hψ 1 (Or.inl rfl) 2]
        simpa using h2
    · refine ⟨2, by simp, 3, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        constructor
        · have : eqLo 1 (fun n : ℕ => (n : ℤ)) 2 = 2 := by
            rw [show (2:ℕ) = 1 + 1 from rfl, eqLo_succ _ _ 1 le_rfl]; simp
          rw [this]; norm_num
        · norm_num
      · rw [hψ 2 (Or.inr rfl) 3]
        simpa using h3


/-- The smallness hypothesis of `volterra_multi_instance_perturbed` is satisfiable with `ε > 0`: `θ = π/2` and `cos θ' = 1/100`. -/
lemma volterra_multi_perturbed_params :
    ∃ θ θ' : ℝ, Real.sin θ ≠ 0 ∧ Real.sin θ' ≠ 0 ∧ Real.cos θ ≠ Real.cos θ' ∧
      2 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|) ≤ 1 / 5 := by
  refine ⟨Real.pi / 2, Real.arccos (1 / 100), ?_, ?_, ?_, ?_⟩
  · simp
  · rw [Real.sin_arccos]
    have : (0 : ℝ) < 1 - (1 / 100) ^ 2 := by norm_num
    exact (Real.sqrt_pos.mpr this).ne'
  · rw [Real.cos_arccos (by norm_num) (by norm_num)]
    simp
  · rw [Real.cos_arccos (by norm_num) (by norm_num), Real.cos_pi_div_two, Real.sin_arccos]
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 - (1 / 100) ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hpos : 0 < Real.sqrt (1 - (1 / 100) ^ 2) := lt_of_lt_of_le (by norm_num) hs
    rw [abs_of_pos hpos]
    rw [show |2 * (1 / 100 : ℝ) - 2 * 0| = 1 / 50 by norm_num]
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith

/-- A constant pair with a nonzero Casoratian determinant has the identity transfer matrix. -/
lemma transMat_const_one (f g : ℤ → ℝ) (jj : ℕ → ℤ)
    (hdet : f (jj 1) * g (jj 1 + 1) - g (jj 1) * f (jj 1 + 1) ≠ 0) :
    transMat (fun _ => f) (fun _ => g) jj 1 = 1 := by
  unfold transMat
  have hU : (bondMat (fun _ => f) (fun _ => g) (1 + 1) (jj 1)).det ≠ 0 := by
    show (bondMat (fun _ => f) (fun _ => g) 1 (jj 1)).det ≠ 0
    unfold bondMat
    rw [Matrix.det_fin_two_of]
    exact hdet
  exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU)

/-! ### A hard-edge instance (`s₀ = 0`, `A(-1) = 0`) -/

/-- The hard-edge bond coefficient: `A_j = 1` except `A_{-1} = 0`. -/
def heA (j : ℤ) : ℝ := if j = -1 then 0 else 1

/-- The hard-edge solution family `i ↦ sin((i+1)α)` (it vanishes at the ghost site `i = -1`). -/
noncomputable def heSin (α : ℝ) (i : ℤ) : ℝ := Real.sin (((i : ℝ) + 1) * α)

/-- The second family `i ↦ cos((i+1)α)`. -/
noncomputable def heCos (α : ℝ) (i : ℤ) : ℝ := Real.cos (((i : ℝ) + 1) * α)

lemma heA_nonneg (k : ℤ) (hk : 0 ≤ k) : heA k = 1 := by
  unfold heA
  split_ifs with h0
  · omega
  · rfl

lemma heA_pred (k : ℤ) (hk : 1 ≤ k) : heA (k - 1) = 1 := by
  unfold heA
  split_ifs with h0
  · omega
  · rfl

lemma Lop_heSin (θ α : ℝ) (k : ℤ) (hk : 0 ≤ k) :
    Lop heA (fun _ => 2 * Real.cos θ) (heSin α) k = (2 * Real.cos α - 2 * Real.cos θ) * Real.sin (((k : ℝ) + 1) * α) := by
  have e1 : (((k + 1 : ℤ) : ℝ) + 1) * α = ((k : ℝ) + 1) * α + α := by push_cast; ring
  have e2 : (((k - 1 : ℤ) : ℝ) + 1) * α = ((k : ℝ) + 1) * α - α := by push_cast; ring
  have hghost : heA (k - 1) * heSin α (k - 1) = heSin α (k - 1) := by
    by_cases h0 : k = 0
    · subst h0
      simp [heSin]
    · rw [heA_pred k (by omega), one_mul]
  unfold Lop
  rw [heA_nonneg k hk, hghost]
  simp only [heSin, e1, e2, Real.sin_add, Real.sin_sub]
  ring

lemma Lop_heCos (θ α : ℝ) (k : ℤ) (hk : 1 ≤ k) :
    Lop heA (fun _ => 2 * Real.cos θ) (heCos α) k = (2 * Real.cos α - 2 * Real.cos θ) * Real.cos (((k : ℝ) + 1) * α) := by
  have e1 : (((k + 1 : ℤ) : ℝ) + 1) * α = ((k : ℝ) + 1) * α + α := by push_cast; ring
  have e2 : (((k - 1 : ℤ) : ℝ) + 1) * α = ((k : ℝ) + 1) * α - α := by push_cast; ring
  unfold Lop
  rw [heA_nonneg k (by omega), heA_pred k hk]
  simp only [heCos, e1, e2, Real.cos_add, Real.cos_sub]
  ring

lemma cas_heSin_heCos (α : ℝ) (j : ℤ) (hj : 0 ≤ j) : cas heA (heSin α) (heCos α) j = Real.sin α := by
  unfold cas
  rw [heA_nonneg j hj]
  have e1 : (((j + 1 : ℤ) : ℝ) + 1) * α = ((j : ℝ) + 1) * α + α := by push_cast; ring
  simp only [heSin, heCos, e1, Real.sin_add, Real.cos_add]
  have := Real.sin_sq_add_cos_sq (((j : ℝ) + 1) * α)
  linear_combination (Real.sin α) * this

lemma abs_Lh_heSin (h θ α : ℝ) (hh : 0 < h) (k : ℤ) (hk : 0 ≤ k) :
    |Lh h heA (fun _ => 2 * Real.cos θ) (heSin α) k| ≤ |2 * Real.cos α - 2 * Real.cos θ| / h := by
  unfold Lh
  rw [Lop_heSin θ α k hk, abs_mul, abs_mul, abs_inv, abs_of_pos hh, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))
    (inv_nonneg.mpr hh.le)

lemma abs_Lh_heCos (h θ α : ℝ) (hh : 0 < h) (k : ℤ) (hk : 1 ≤ k) :
    |Lh h heA (fun _ => 2 * Real.cos θ) (heCos α) k| ≤ |2 * Real.cos α - 2 * Real.cos θ| / h := by
  unfold Lh
  rw [Lop_heCos θ α k hk, abs_mul, abs_mul, abs_inv, abs_of_pos hh, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (inv_nonneg.mpr hh.le)

/-- The exact hard-edge solution `ψ_i = (sinθ'/sinθ) sin((i+1)θ)`, seed `ψ_0 = sinθ' = φ¹_0`. -/
noncomputable def heSol (θ θ' : ℝ) (i : ℤ) : ℝ := (Real.sin θ' / Real.sin θ) * heSin θ i

lemma Lh_heSol (h θ θ' : ℝ) (k : ℤ) (hk : 0 ≤ k) :
    Lh h heA (fun _ => 2 * Real.cos θ) (heSol θ θ') k = 0 := by
  unfold Lh
  have : Lop heA (fun _ => 2 * Real.cos θ) (heSol θ θ') k
      = (Real.sin θ' / Real.sin θ) * Lop heA (fun _ => 2 * Real.cos θ) (heSin θ) k := by
    simp only [Lop, heSol]; ring
  rw [this, Lop_heSin θ θ k hk]
  simp

/-- **Perturbed multi-patch instance, hard-edge seed** (`s₀ = 0`, `A_{-1} = 0`; `ε > 0`, `ψ ≠ ψ̂`).  Two patches
(`j_p = p`, `N_R = 3`, equation sites `[0,1]` and `[2,2]`), `A = heA`, `Q = 2cosθ`, the pair `φ¹ = sin((i+1)θ')`,
`φ² = cos((i+1)θ')` on both patches (`M_1 = I`, `ψ̂_p = φ¹`; the second member does not solve the hard-edge equation at
`i = 0`, which is the exempted residual `r²_{1,0}`), and the exact hard-edge solution `ψ_i = (sinθ'/sinθ) sin((i+1)θ)`
with seed `ψ_0 = φ¹_0`.  `εΘ = 3|2cosθ'-2cosθ|/|sinθ'|`; the smallness `εΘ ≤ 1/5` is a hypothesis. -/
theorem volterra_multi_instance_hard_edge (h θ θ' : ℝ) (hh : 0 < h) (hθ : Real.sin θ ≠ 0)
    (hθ' : Real.sin θ' ≠ 0) (hne : Real.cos θ ≠ Real.cos θ')
    (hsmall : 3 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|) ≤ 1 / 5) :
    0 < |2 * Real.cos θ' - 2 * Real.cos θ| / h ∧
    (∀ p ∈ Icc 1 2, ∀ j ∈ Icc (eqLo 0 (fun n : ℕ => (n : ℤ)) p) ((p : ℤ) + 1),
      |heSol θ θ' j - psiHat (fun _ => heSin θ') (fun _ => heCos θ') (fun n : ℕ => (n : ℤ)) p j|
        ≤ 832 * (3 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|))) ∧
    (∃ p ∈ Icc 1 2, ∃ j ∈ Icc (eqLo 0 (fun n : ℕ => (n : ℤ)) p) ((p : ℤ) + 1),
      heSol θ θ' j ≠ psiHat (fun _ => heSin θ') (fun _ => heCos θ') (fun n : ℕ => (n : ℤ)) p j) := by
  have hω : 0 < |Real.sin θ'| := abs_pos.mpr hθ'
  have hεpos : 0 < |2 * Real.cos θ' - 2 * Real.cos θ| / h :=
    div_pos (abs_pos.mpr (by intro h'; apply hne; linarith)) hh
  have hdet : heSin θ' (((fun n : ℕ => (n : ℤ)) 1)) * heCos θ' (((fun n : ℕ => (n : ℤ)) 1) + 1)
      - heCos θ' (((fun n : ℕ => (n : ℤ)) 1)) * heSin θ' (((fun n : ℕ => (n : ℤ)) 1) + 1) ≠ 0 := by
    have h1 : cas heA (heSin θ') (heCos θ') 1 = Real.sin θ' := cas_heSin_heCos θ' 1 (by norm_num)
    unfold cas at h1
    rw [heA_nonneg 1 (by norm_num), one_mul] at h1
    intro h0
    apply hθ'
    simp only [Nat.cast_one] at h0
    linarith
  have hT1 := transMat_const_one (heSin θ') (heCos θ') (fun n : ℕ => (n : ℤ)) hdet
  have hεΘ : |2 * Real.cos θ' - 2 * Real.cos θ| / h * (h / |Real.sin θ'| * 3)
      = 3 * (|2 * Real.cos θ' - 2 * Real.cos θ| / |Real.sin θ'|) := by
    field_simp
  have heqLo : ∀ p ∈ Icc 1 2, 0 ≤ eqLo 0 (fun n : ℕ => (n : ℤ)) p := by
    intro p hp
    have hp' := Finset.mem_Icc.mp hp
    rcases (show p = 1 ∨ p = 2 by omega) with rfl | rfl
    · rw [eqLo_one]
    · rw [show (2:ℕ) = 1 + 1 from rfl, eqLo_succ _ _ 1 le_rfl]; simp
  have key := volterra_multi (h := h) (ω := |Real.sin θ'|) (cm := 1) (CE := 1) (K := 1)
    (ε := |2 * Real.cos θ' - 2 * Real.cos θ| / h) (Λ := 1)
    (A := heA) (Q := fun _ => 2 * Real.cos θ) (ψ := heSol θ θ')
    (ρ := fun _ => 1) (M := fun _ => 1) (W := fun _ => 1) (s0 := 0) (NR := 3) (P := 2)
    (jj := fun n : ℕ => (n : ℤ)) (φ1 := fun _ => heSin θ') (φ2 := fun _ => heCos θ')
    (hh := hh) (hω := hω) (hcm := one_pos) (hK := zero_le_one) (hε := hεpos.le) (hΛ := le_rfl)
    (hP := by norm_num) (hjj0 := rfl) (hjjmono := fun p _ => by simp) (hjjP := by norm_num)
    (hs0 := Or.inl rfl) (hA := fun _ => by simp [heA])
    (hS1 := fun p _ j hj => by
      have hj0 : 0 ≤ j := by
        have := (Finset.mem_Icc.mp hj).1
        have h0 : (0:ℤ) ≤ ((fun n : ℕ => (n : ℤ)) (p - 1)) := by simp
        exact h0.trans this
      show 1 * |Real.sin θ'| ≤ |cas heA (heSin θ') (heCos θ') j|
      rw [cas_heSin_heCos θ' j hj0, one_mul])
    (hMpos := fun j _ => one_pos) (hWpos := fun j _ => one_pos)
    (hmono := fun k _ j _ _ => by norm_num)
    (hφ1 := fun p _ j _ => by
      show |Real.sin (((j : ℝ) + 1) * θ')| ≤ 1 * 1 * 1
      rw [mul_one, mul_one]
      exact Real.abs_sin_le_one _)
    (hφ2 := fun p _ j _ => by
      show |Real.cos (((j : ℝ) + 1) * θ')| ≤ 1 * (1 : ℝ)⁻¹ * 1
      rw [inv_one, mul_one, mul_one]
      exact Real.abs_cos_le_one _)
    (hρ := fun _ => zero_le_one)
    (hr1 := fun p hp k hk => by
      have hk0 : 0 ≤ k := (heqLo p hp).trans (Finset.mem_Icc.mp hk).1
      show |Lh h heA (fun _ => 2 * Real.cos θ) (heSin θ') k| ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h * 1 * 1 * 1
      simpa only [mul_one] using abs_Lh_heSin h θ θ' hh k hk0)
    (hr2 := fun p hp k hk hk0' => by
      have hk1 : 1 ≤ k := by
        have := (heqLo p hp).trans (Finset.mem_Icc.mp hk).1
        omega
      show |Lh h heA (fun _ => 2 * Real.cos θ) (heCos θ') k|
        ≤ |2 * Real.cos θ' - 2 * Real.cos θ| / h * 1 * (1 : ℝ)⁻¹ * 1
      simpa only [mul_one, inv_one] using abs_Lh_heCos h θ θ' hh k hk1)
    (hT := fun p hp1 hp2 => by
      have hp : p = 1 := by omega
      subst hp
      rw [hT1, Matrix.det_one]
      simp)
    (hsol := fun k hk => Lh_heSol h θ θ' k (Finset.mem_Icc.mp hk).1)
    (hseed := fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      have hj0 : j = 0 := by omega
      subst hj0
      show (Real.sin θ' / Real.sin θ) * Real.sin ((((0:ℤ) : ℝ) + 1) * θ) = Real.sin ((((0:ℤ) : ℝ) + 1) * θ')
      simp [div_mul_cancel₀ _ hθ])
    (hsmall := by
      rw [volTheta_hard_edge, hεΘ, mvCstar_inst]
      exact hsmall)
  have hψ := psiHat_eq_phi1_of_trans_one (fun _ => heSin θ') (fun _ => heCos θ')
    (fun n : ℕ => (n : ℤ)) hT1
  refine ⟨hεpos, ?_, ?_⟩
  · intro p hp j hj
    have hb := key.1 p hp j hj
    rw [volTheta_hard_edge, hεΘ, mvC_inst] at hb
    simpa using hb
  · refine ⟨1, by simp, 1, ?_, ?_⟩
    · rw [eqLo_one]; simp
    · rw [hψ 1 (Or.inl rfl) 1]
      intro heq
      have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      have hs2' : Real.sin (2 * θ') = 2 * Real.sin θ' * Real.cos θ' := Real.sin_two_mul θ'
      simp only [heSol, heSin, Int.cast_one] at heq
      rw [show ((1:ℝ) + 1) * θ = 2 * θ by ring, show ((1:ℝ) + 1) * θ' = 2 * θ' by ring, hs2, hs2'] at heq
      apply hne
      have h3 := heq
      field_simp at h3
      exact h3


/-- info: 'FormalResearch.JE.volterra_multi_instance_perturbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi_instance_perturbed

/-- info: 'FormalResearch.JE.volterra_multi_instance_hard_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi_instance_hard_edge

/-- info: 'FormalResearch.JE.volterra_multi_perturbed_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi_perturbed_params

/-- info: 'FormalResearch.JE.volterra_multi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi

/-- info: 'FormalResearch.JE.volterra_multi_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi_instance

/-- info: 'FormalResearch.JE.transfer_of_forbidden_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.transfer_of_forbidden_overlap

/-- info: 'FormalResearch.JE.volterra_multi_forbidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.volterra_multi_forbidden

/-- info: 'FormalResearch.JE.patch_volterra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.patch_volterra

/-- info: 'FormalResearch.JE.flux_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.flux_transfer

/-- info: 'FormalResearch.JE.cvec_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.cvec_bounds

/-- info: 'FormalResearch.JE.psiHat_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.psiHat_overlap

/-- info: 'FormalResearch.JE.covering_patch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.covering_patch

end FormalResearch.JE

end
