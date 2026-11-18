module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.SoftAssembly6
public import FormalResearch.JacobiEigenvectors.TheoremA.WindowMass2

/-!
# Paper J, Layer 3 (L3.3, part 1): the fold row of a soft edge, `lem:tha-Mflat` (flat0), and the half-window masses (flat1)

Source: Paper J `app_thmB.tex`, "Splices, half-windows and collars", proof of `lem:tha-Mflat`, paragraphs *The fold row* and *Half-windows* (`eq:tha-flatZ`, `eq:tha-flat0`, `eq:tha-flat1`).

Chain of lemmas (checked against the paper):
1. `muS0_two_sided`: `cmu0 |alpha| <= |mu_0(alpha)| <= Cmu0 |alpha|` on `|alpha| <= delta_0` (`mu0_zero`, `mu0_slope`, mean value theorem).
2. `zeta_lip0`: `|zeta(x;alpha)| <= c_Z |alpha| + d_+ |x|` on `|x| <= 2 eta` (`zeta_alpha`, `zeta_mvt`).
3. `fold_real` (pure real analysis of `eq:tha-flatZ`): from `|mu~ - mu_0| <= Q h`, `a = -mu~/h`, `a <= 1` and the smallness `SoftFoldSmall`,
   `|zeta|/sqrt h <= sqrt(max(-a,0)) + C_f sqrt h`.
4. `fold_Z_bound`: `|Z_{n_0}| <= sqrt(max(-a,0)) + C_f sqrt h` for every row `n_0` with `|u_{n_0} - u_c| <= h/2` (so for `n_c = nearestRow u_c`): **flat0**.
5. `fold_in_window`: `C_f sqrt h <= l_A` for small `h` (`ell_sixth`), hence `n_0 in Omega`; and `C_f sqrt h <= l_A / 4`, so `|Z_{n_0}| <= s_A` (`wmCut`).
6. `flat_half_masses`: the three half-window mass bounds of **flat1** from `propThaM_of_facts` at the cut `s = Z_{n_0}`, with `Omega_- = {n in Omega : n <= n_0}` equal to `{Z_n <= Z_{n_0}}` (`Zof_le`, the collar monotonicity; window rows are inside `|u_n - u_c| < eta/4`).

## Differences from the paper

* **FINDING (chart constants).**  The paper chooses `delta_0` with `C_Z sqrt(C_mu delta_0) <= 1` ("choosing `delta_0` ..."); in `SoftEdgeChart` the data `delta_0, c_Z, cmu0, Cmu0` are
  unrelated, and for `a <= 0` and a chart with `2 c_Z^2 Cmu0 delta_0 > cmu0^2` (take `zeta(0;alpha) = c_Z alpha`, `mu_0 = cmu0 alpha`, all other fields unchanged) one has
  `|Z_{n_c}| ~ c_Z alpha/sqrt h` against `2 sqrt A ~ 2 sqrt(cmu0 alpha/h)`, so `n_c` is **not** in the window and flat0 fails.  The hypothesis is made explicit as the
  chart-constant statement `SoftFoldSmall C : 2 c_Z^2 Cmu0 delta_0 <= cmu0^2`; minimal correction: add it to `SoftEdgeChart` as a field (paper's form: `delta_0` small against the chart constants).
* The theorems are stated for any row `n_0` with `|u_{n_0} - u_c| <= h/2` (`nearestRow` lives in `TheoremB`); `SoftMflat2` specialises.

## Not formalised

flat2 (the seam rows), see `SoftMflat2.lean`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts
  FormalResearch.JacobiEigenvectors.Engine

variable {Par : Type*} [TopologicalSpace Par]

section Fold

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **Chart-constant smallness** (the paper's "choose `delta_0` with `C_Z sqrt(C_mu delta_0) <= 1`", `app_thmB`, proof of `lem:tha-Mflat`): `2 c_Z^2 Cmu0 delta_0 <= cmu0^2`.  Not a field of `SoftEdgeChart`
(see the finding in the module docstring). -/
def SoftFoldSmall : Prop := 2 * C.cZ ^ 2 * C.Cmu0 * C.δ0 ≤ C.cmu0 ^ 2

/-- `cmu0 |alpha| <= |mu_0(alpha)| <= Cmu0 |alpha|` on `|alpha| <= delta_0`. -/
lemma muS0_two_sided {μ : Par × ℝ} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) :
    C.cmu0 * |α| ≤ |C.muS 0 μ α| ∧ |C.muS 0 μ α| ≤ C.Cmu0 * |α| := by
  obtain ⟨hc0, hcC⟩ := C.consts_pos5
  have hδ : 0 < C.δ0 := C.consts_pos.1
  have hdiff : Differentiable ℝ (C.muS 0 μ) := (C.mu0_deriv μ hμ).1.differentiable (by norm_num)
  have hD : Convex ℝ (Set.Icc (-C.δ0) C.δ0) := convex_Icc _ _
  have hlow : ∀ x ∈ interior (Set.Icc (-C.δ0) C.δ0), C.cmu0 ≤ deriv (C.muS 0 μ) x := by
    intro x hx
    rw [interior_Icc] at hx
    exact (C.mu0_slope μ hμ x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)).1
  have hup : ∀ x ∈ interior (Set.Icc (-C.δ0) C.δ0), deriv (C.muS 0 μ) x ≤ C.Cmu0 := by
    intro x hx
    rw [interior_Icc] at hx
    exact (C.mu0_slope μ hμ x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)).2
  have hm1 := hD.mul_sub_le_image_sub_of_le_deriv (f := C.muS 0 μ) (C := C.cmu0) hdiff.continuous.continuousOn
    hdiff.differentiableOn hlow
  have hm2 := hD.image_sub_le_mul_sub_of_deriv_le (f := C.muS 0 μ) (C := C.Cmu0) hdiff.continuous.continuousOn
    hdiff.differentiableOn hup
  have h0 : (0 : ℝ) ∈ Set.Icc (-C.δ0) C.δ0 := Set.mem_Icc.mpr ⟨by linarith, hδ.le⟩
  have hαm : α ∈ Set.Icc (-C.δ0) C.δ0 := Set.mem_Icc.mpr (abs_le.mp hα)
  have hz := C.mu0_zero μ hμ
  rcases le_total 0 α with hα0 | hα0
  · have a1 := hm1 0 h0 α hαm hα0
    have a2 := hm2 0 h0 α hαm hα0
    rw [hz] at a1 a2
    rw [abs_of_nonneg hα0, abs_of_nonneg (by nlinarith)]
    constructor <;> nlinarith
  · have a1 := hm1 α hαm 0 h0 hα0
    have a2 := hm2 α hαm 0 h0 hα0
    rw [hz] at a1 a2
    rw [abs_of_nonpos hα0, abs_of_nonpos (by nlinarith)]
    constructor <;> nlinarith

/-- `|zeta(x;alpha)| <= c_Z |alpha| + d_+ |x|` on `|x| <= 2 eta`. -/
lemma zeta_lip0 {μ : Par × ℝ} (hμ : μ ∈ P) {α : ℝ} (hα : |α| ≤ C.δ0) {x : ℝ} (hx : |x| ≤ 2 * C.η) :
    |C.zeta μ α x| ≤ C.cZ * |α| + C.dp * |x| := by
  obtain ⟨-, hη, hdm, hdmp, -, -, -, hcZ⟩ := C.consts_pos
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hz0 := C.zeta_alpha μ hμ α hα
  have hx' := abs_le.mp hx
  rcases le_total 0 x with hx0 | hx0
  · have hm := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ 0) hx0 (by linarith)
    have h1 := abs_le.mp hz0
    rw [abs_of_nonneg hx0]
    have h3 := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ x - 0)
    rw [abs_le]; constructor <;> nlinarith [hm.1, hm.2]
  · have hm := C.zeta_mvt hμ hα (by linarith : -(2 * C.η) ≤ x) hx0 (by linarith)
    have h1 := abs_le.mp hz0
    rw [abs_of_nonpos hx0]
    have h3 := mul_nonneg hdm.le (by linarith : (0 : ℝ) ≤ 0 - x)
    rw [abs_le]; constructor <;> nlinarith [hm.1, hm.2]

end Fold

/-! ### The real analysis of `eq:tha-flatZ` -/

/-- **The fold-row estimate, abstract** (`eq:tha-flatZ`, `eq:tha-flat0`): with `mu~ = -a h`, `|mu~ - mu_0| <= Q h`, `cmu |alpha| <= |mu_0| <= Cmu |alpha|`, `|zeta_x| <= cZ |alpha| + dp (h/2)`,
the smallness `2 cZ^2 Cmu delta <= cmu^2`, `(Q+1) h <= Cmu delta` and `a <= 1`: `|zeta_x| / sqrt h <= sqrt(max(-a,0)) + (cZ (1+Q)/cmu + dp/2) sqrt h`. -/
theorem fold_real (h δ cZ cmu Cmu Q dp a α μ0 μt ζx : ℝ) (hh : 0 < h) (hQ0 : 0 ≤ Q) (hcm : 0 < cmu) (hcmC : cmu ≤ Cmu) (hδ : 0 < δ)
    (hcZ : 0 ≤ cZ) (hdp : 0 ≤ dp) (hsmall : 2 * cZ ^ 2 * Cmu * δ ≤ cmu ^ 2) (hhs : (Q + 1) * h ≤ Cmu * δ)
    (hα : |α| ≤ δ) (hlow : cmu * |α| ≤ |μ0|) (hup : |μ0| ≤ Cmu * |α|) (hμt : |μt - μ0| ≤ Q * h) (ha : a = -(1 / h) * μt) (ha1 : a ≤ 1)
    (hζ : |ζx| ≤ cZ * |α| + dp * (h / 2)) :
    |ζx| / Real.sqrt h ≤ Real.sqrt (max (-a) 0) + (cZ * (1 + Q) / cmu + dp / 2) * Real.sqrt h := by
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hss : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  have hCm : 0 < Cmu := lt_of_lt_of_le hcm hcmC
  have hμe : μt = -a * h := by rw [ha]; field_simp
  have hμabs : |μt| = |a| * h := by rw [hμe, abs_mul, abs_neg, abs_of_pos hh]
  have hαb : cmu * |α| ≤ (|a| + Q) * h := by
    have h1 : |μ0| ≤ |μt| + Q * h := by
      have h' := abs_sub_abs_le_abs_sub μ0 μt
      rw [abs_sub_comm] at h'
      linarith
    rw [hμabs] at h1
    linarith [hlow, h1, (by ring : (|a| + Q) * h = |a| * h + Q * h)]
  have hζb : |ζx| ≤ cZ * ((|a| + Q) * h) / cmu + dp * (h / 2) := by
    have : cZ * |α| ≤ cZ * ((|a| + Q) * h) / cmu := by
      rw [le_div_iff₀ hcm]
      calc cZ * |α| * cmu = cZ * (cmu * |α|) := by ring
        _ ≤ cZ * ((|a| + Q) * h) := mul_le_mul_of_nonneg_left hαb hcZ
    linarith
  have hdiv : |ζx| / Real.sqrt h ≤ (cZ * (|a| + Q) / cmu) * Real.sqrt h + (dp / 2) * Real.sqrt h := by
    rw [div_le_iff₀ hs]
    have e1 : cZ * ((|a| + Q) * h) / cmu = (cZ * (|a| + Q) / cmu) * Real.sqrt h * Real.sqrt h := by
      calc cZ * ((|a| + Q) * h) / cmu = cZ * (|a| + Q) / cmu * h := by ring
        _ = cZ * (|a| + Q) / cmu * (Real.sqrt h * Real.sqrt h) := by rw [hss]
        _ = _ := by ring
    have e2 : dp * (h / 2) = (dp / 2) * Real.sqrt h * Real.sqrt h := by
      calc dp * (h / 2) = dp / 2 * h := by ring
        _ = dp / 2 * (Real.sqrt h * Real.sqrt h) := by rw [hss]
        _ = _ := by ring
    have e3 : ((cZ * (|a| + Q) / cmu) * Real.sqrt h + (dp / 2) * Real.sqrt h) * Real.sqrt h =
        (cZ * (|a| + Q) / cmu) * Real.sqrt h * Real.sqrt h + (dp / 2) * Real.sqrt h * Real.sqrt h := by ring
    rw [e3, ← e1, ← e2]
    exact hζb
  have hfin : (cZ * (1 + Q) / cmu + dp / 2) * Real.sqrt h = (cZ * (1 + Q) / cmu) * Real.sqrt h + (dp / 2) * Real.sqrt h := by ring
  have hsp : cZ * (|a| + Q) / cmu * Real.sqrt h = (cZ * |a| / cmu) * Real.sqrt h + (cZ * Q / cmu) * Real.sqrt h := by ring
  by_cases ha0 : a ≤ 0
  · have hA : max (-a) 0 = -a := max_eq_left (by linarith)
    rw [hA]
    have habs : |a| = -a := abs_of_nonpos ha0
    have hAh : (-a) * h ≤ 2 * (Cmu * δ) := by
      have h1 : -a * h = μt := by rw [hμe]
      have h2 : μt ≤ |μt| := le_abs_self _
      have h3 : |μt| ≤ |μ0| + Q * h := by
        have h' := abs_sub_abs_le_abs_sub μt μ0
        linarith [hμt]
      have h4 : |μ0| ≤ Cmu * δ := hup.trans (mul_le_mul_of_nonneg_left hα hCm.le)
      have h5 : Q * h ≤ Cmu * δ := by
        have : (Q + 1) * h = Q * h + h := by ring
        linarith
      linarith
    have hAn : 0 ≤ -a := by linarith
    set sA := Real.sqrt (-a) with hsA
    have hsA2 : sA * sA = -a := Real.mul_self_sqrt hAn
    have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
    have hkey : cZ * sA * Real.sqrt h ≤ cmu := by
      by_contra hcon
      push_neg at hcon
      have hsq : cmu ^ 2 < (cZ * sA * Real.sqrt h) ^ 2 := pow_lt_pow_left₀ hcon hcm.le (by norm_num : (2 : ℕ) ≠ 0)
      have e : (cZ * sA * Real.sqrt h) ^ 2 = cZ ^ 2 * ((-a) * h) := by
        have : (cZ * sA * Real.sqrt h) ^ 2 = cZ ^ 2 * (sA * sA) * (Real.sqrt h * Real.sqrt h) := by ring
        rw [this, hsA2, hss]; ring
      rw [e] at hsq
      have h6 : cZ ^ 2 * ((-a) * h) ≤ cZ ^ 2 * (2 * (Cmu * δ)) := mul_le_mul_of_nonneg_left hAh (sq_nonneg _)
      linarith [hsq, h6, hsmall, (by ring : cZ ^ 2 * (2 * (Cmu * δ)) = 2 * cZ ^ 2 * Cmu * δ)]
    have hterm : (cZ * |a| / cmu) * Real.sqrt h ≤ sA := by
      rw [habs]
      have e : cZ * (-a) / cmu * Real.sqrt h = sA * (cZ * sA * Real.sqrt h / cmu) := by
        rw [← hsA2]; field_simp
      rw [e]
      have h1 : cZ * sA * Real.sqrt h / cmu ≤ 1 := by rw [div_le_one hcm]; exact hkey
      calc sA * (cZ * sA * Real.sqrt h / cmu) ≤ sA * 1 := mul_le_mul_of_nonneg_left h1 hsA0
        _ = sA := mul_one _
    have hQ : cZ * Q / cmu ≤ cZ * (1 + Q) / cmu := by
      apply div_le_div_of_nonneg_right _ hcm.le
      exact mul_le_mul_of_nonneg_left (by linarith) hcZ
    have hQs : (cZ * Q / cmu) * Real.sqrt h ≤ (cZ * (1 + Q) / cmu) * Real.sqrt h := mul_le_mul_of_nonneg_right hQ hs.le
    linarith [hdiv, hsp, hterm, hQs, hfin]
  · push_neg at ha0
    have hA : max (-a) 0 = 0 := max_eq_right (by linarith)
    rw [hA, Real.sqrt_zero, zero_add]
    have habs : |a| = a := abs_of_pos ha0
    have hle : cZ * (|a| + Q) / cmu ≤ cZ * (1 + Q) / cmu := by
      apply div_le_div_of_nonneg_right _ hcm.le
      rw [habs]
      exact mul_le_mul_of_nonneg_left (by linarith) hcZ
    have := mul_le_mul_of_nonneg_right hle hs.le
    linarith [hdiv, this, hfin]

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.fold_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fold_real

/-- **`C sqrt h <= l_A / 4`** for small `h`: `4 C_f sqrt h <= (1 + A)^{-1/6}` when `A h <= B` (`l_A >= c h^{1/6}`, `eq:tha-flat1`'s `C sqrt h <= l_A / 4`). -/
theorem sqrt_le_ell (Cf B h A : ℝ) (hCf : 0 ≤ Cf) (hB : 0 ≤ B) (hh : 0 < h) (hh1 : h ≤ 1) (hA : 0 ≤ A) (hAh : A * h ≤ B)
    (hs : 4096 * Cf ^ 6 * (1 + B) * h ≤ 1) : 4 * Cf * Real.sqrt h ≤ (1 + A) ^ (-(1 : ℝ) / 6) := by
  have hr0 : 0 < (1 + A) ^ ((1 : ℝ) / 6) := Real.rpow_pos_of_pos (by linarith) _
  have hr6 : ((1 + A) ^ ((1 : ℝ) / 6)) ^ 6 = 1 + A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hrneg : (1 + A) ^ (-(1 : ℝ) / 6) = ((1 + A) ^ ((1 : ℝ) / 6))⁻¹ := by
    rw [← Real.rpow_neg (by linarith)]; norm_num
  have hsq : Real.sqrt h ^ 6 = h ^ 3 := by
    have : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
    calc Real.sqrt h ^ 6 = (Real.sqrt h ^ 2) ^ 3 := by ring
      _ = h ^ 3 := by rw [this]
  set r := (1 + A) ^ ((1 : ℝ) / 6) with hr
  have hx6 : (4 * Cf * Real.sqrt h * r) ^ 6 ≤ 1 := by
    have e : (4 * Cf * Real.sqrt h * r) ^ 6 = 4096 * Cf ^ 6 * h ^ 3 * (1 + A) := by
      have : (4 * Cf * Real.sqrt h * r) ^ 6 = 4 ^ 6 * Cf ^ 6 * Real.sqrt h ^ 6 * r ^ 6 := by ring
      rw [this, hsq, hr6]; norm_num
    rw [e]
    have h1 : h * (1 + A) ≤ 1 + B := by nlinarith
    have h2 : 4096 * Cf ^ 6 * h ^ 3 * (1 + A) = (4096 * Cf ^ 6 * h ^ 2) * (h * (1 + A)) := by ring
    rw [h2]
    have h3 : 0 ≤ 4096 * Cf ^ 6 * h ^ 2 := by positivity
    calc (4096 * Cf ^ 6 * h ^ 2) * (h * (1 + A)) ≤ (4096 * Cf ^ 6 * h ^ 2) * (1 + B) := mul_le_mul_of_nonneg_left h1 h3
      _ = (4096 * Cf ^ 6 * (1 + B) * h) * h := by ring
      _ ≤ 1 * 1 := mul_le_mul hs hh1 hh.le (by norm_num)
      _ = 1 := by norm_num
  have hx0 : 0 ≤ 4 * Cf * Real.sqrt h * r := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCf) (Real.sqrt_nonneg _)) hr0.le
  have hx1 : 4 * Cf * Real.sqrt h * r ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have := one_lt_pow₀ hcon (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  rw [hrneg]
  calc 4 * Cf * Real.sqrt h = (4 * Cf * Real.sqrt h * r) * r⁻¹ := by field_simp
    _ ≤ 1 * r⁻¹ := mul_le_mul_of_nonneg_right hx1 (inv_nonneg.mpr hr0.le)
    _ = r⁻¹ := one_mul _

section FoldChart

variable {Fz : SymbolFamily (Par × ℝ)} {P : Set (Par × ℝ)} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {Lm : ℝ → ℝ}
  (C : SoftEdgeChart Fz P m q U V Lm)

/-- **flat0** (`eq:tha-flat0`): for every row `n_0` with `|u_{n_0} - u_c| <= h/2` and `a <= 1`, `|Z_{n_0}| <= sqrt(max(-a,0)) + C_f sqrt h`.  Needs `SoftFoldSmall` (see the module docstring). -/
theorem fold_Z_bound (hsmall : SoftFoldSmall C) :
    ∃ Cf h0 : ℝ, 0 < Cf ∧ 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, Fz.step N ≤ h0 → C.aOf p X N ≤ 1 →
      ∀ n0 : ℤ, |uNode (Fz.step N) n0 - C.uc p| ≤ Fz.step N / 2 →
        |C.Zof p X N n0| ≤ Real.sqrt (max (-C.aOf p X N) 0) + Cf * Real.sqrt (Fz.step N) := by
  obtain ⟨hδ, hη, hdm, hdmp, -, -, -, hcZ⟩ := C.consts_pos
  obtain ⟨hc0, hcC⟩ := C.consts_pos5
  have hdp : 0 < C.dp := lt_of_lt_of_le hdm hdmp
  have hCm : 0 < C.Cmu0 := lt_of_lt_of_le hc0 hcC
  have hQ0 : 0 ≤ ((q / 2 : ℕ) : ℝ) * C.Cmu := mul_nonneg (Nat.cast_nonneg _) C.consts_pos2.1
  set Q : ℝ := ((q / 2 : ℕ) : ℝ) * C.Cmu with hQ
  refine ⟨C.cZ * (1 + Q) / C.cmu0 + C.dp / 2 + 1, min (min 1 C.η) (C.Cmu0 * C.δ0 / (Q + 1)), by positivity,
    lt_min (lt_min one_pos hη) (by positivity), ?_⟩
  intro p hp X hX N hstep ha n0 hn0
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hh1 : Fz.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhη : Fz.step N ≤ C.η := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhs : (Q + 1) * Fz.step N ≤ C.Cmu0 * C.δ0 := by
    have := hstep.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hα := C.abs_alpha_le hX
  have hx2 : |uNode (Fz.step N) n0 - C.uc p| ≤ 2 * C.η := by linarith
  have hζ := zeta_lip0 C hp hα hx2
  have hζ' : |C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n0 - C.uc p)| ≤ C.cZ * |Fz.bandHi p - X| + C.dp * (Fz.step N / 2) :=
    hζ.trans (by nlinarith [mul_le_mul_of_nonneg_left hn0 hdp.le])
  obtain ⟨hlow, hup⟩ := muS0_two_sided C hp hα
  have hsub := C.muTilde_sub_le hp hX hh1
  have hfr := fold_real (Fz.step N) C.δ0 C.cZ C.cmu0 C.Cmu0 Q C.dp (C.aOf p X N) (Fz.bandHi p - X) (C.muS 0 p (Fz.bandHi p - X))
    (C.muTilde p X N) (C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n0 - C.uc p)) hh hQ0 hc0 hcC hδ hcZ.le hdp.le hsmall hhs hα hlow hup
    hsub (C.aOf_eq p X N) ha hζ'
  have hZ : C.Zof p X N n0 = C.zeta p (Fz.bandHi p - X) (uNode (Fz.step N) n0 - C.uc p) / Real.sqrt (Fz.step N) := rfl
  rw [hZ, abs_div, abs_of_pos (Real.sqrt_pos.mpr hh)]
  refine hfr.trans ?_
  have hs0 := Real.sqrt_nonneg (Fz.step N)
  nlinarith [hs0]

/-- **The fold row lies in the window, with room to spare** (`n_0 in Omega`, `|Z_{n_0}| <= s_A = sqrt A + l_A / 4`), for `n_0` with `|u_{n_0} - u_c| <= h/2` and `a <= 1`. -/
theorem fold_in_window (hsmall : SoftFoldSmall C) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∀ p ∈ P, ∀ X, |X - Fz.bandHi p| ≤ C.δ0 → ∀ N : ℕ, C.N0 ≤ N → Fz.step N ≤ h0 → C.aOf p X N ≤ 1 →
      ∀ n0 : ℤ, |uNode (Fz.step N) n0 - C.uc p| ≤ Fz.step N / 2 →
        n0 ∈ softWindow C p X N ∧ |C.Zof p X N n0| ≤ wmCut (C.aOf p X N) := by
  obtain ⟨Cf, h1, hCf, hh1p, H⟩ := fold_Z_bound C hsmall
  obtain ⟨hδ, hη, -⟩ := C.consts_pos
  have hBm : 0 ≤ C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) := mul_nonneg C.consts_pos2.1 (by positivity)
  set B : ℝ := C.Cmu * (1 + ((q / 2 : ℕ) : ℝ)) with hB
  refine ⟨min (min h1 1) (min C.η (1 / (4096 * Cf ^ 6 * (1 + B) + 1))), lt_min (lt_min hh1p one_pos) (lt_min hη (by positivity)), ?_⟩
  intro p hp X hX N hN hstep ha n0 hn0
  have hh : 0 < Fz.step N := SoftEdgeChart.step_pos (F := Fz) N
  have hs1 : Fz.step N ≤ h1 := hstep.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : Fz.step N ≤ 1 := hstep.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : Fz.step N ≤ C.η := hstep.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : Fz.step N ≤ 1 / (4096 * Cf ^ 6 * (1 + B) + 1) := hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hK : 4096 * Cf ^ 6 * (1 + B) * Fz.step N ≤ 1 := by
    have h0 : 0 < 4096 * Cf ^ 6 * (1 + B) + 1 := by positivity
    rw [le_div_iff₀ h0] at hs4
    nlinarith
  have hfold := H p hp X hX N hs1 ha n0 hn0
  set A := max (-C.aOf p X N) 0 with hAdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hAh : A * Fz.step N ≤ B := by
    have hmu := C.muTilde_abs_le hp hX hs2
    rcases le_total (C.aOf p X N) 0 with ha0 | ha0
    · have hAe : A = -C.aOf p X N := max_eq_left (by linarith)
      rw [hAe, C.aOf_eq p X N]
      have : -(-(1 / Fz.step N) * C.muTilde p X N) * Fz.step N = C.muTilde p X N := by field_simp
      rw [this]
      exact (le_abs_self _).trans hmu
    · have : A = 0 := max_eq_right (by linarith)
      rw [this]; linarith
  have hell := sqrt_le_ell Cf B (Fz.step N) A hCf.le hBm hh hs2 hA0 hAh hK
  have hsA := Real.sqrt_nonneg A
  refine ⟨?_, ?_⟩
  · -- row membership
    have hrow : n0 ∈ rowsOf N := by
      obtain ⟨huc0, huc1⟩ := C.ucη_in p hp
      have hLs : Fz.step N * ((N : ℝ) + 1) = Fz.L := step_mul_succ Fz N
      have hb := abs_le.mp hn0
      have hu : uNode (Fz.step N) n0 = ((n0 : ℝ) + 1 / 2) * Fz.step N := rfl
      have hpos : 0 < ((n0 : ℝ) + 1 / 2) * Fz.step N := by rw [← hu]; linarith
      have hlt : ((n0 : ℝ) + 1 / 2) * Fz.step N < Fz.step N * ((N : ℝ) + 1) := by rw [hLs, ← hu]; linarith
      have h1' : (0 : ℝ) < (n0 : ℝ) + 1 / 2 := by
        by_contra hc; push_neg at hc; nlinarith
      have h2' : (n0 : ℝ) + 1 / 2 < (N : ℝ) + 1 := by
        by_contra hc; push_neg at hc; nlinarith
      unfold rowsOf
      rw [Finset.mem_Icc]
      constructor
      · have : (-1 : ℝ) < (n0 : ℝ) := by linarith
        exact_mod_cast (show (-1 : ℤ) < n0 by exact_mod_cast this)
      · have : (n0 : ℝ) < (N : ℝ) + 1 := by linarith
        have h3 : n0 < (N : ℤ) + 1 := by exact_mod_cast this
        omega
    unfold softWindow
    rw [Finset.mem_filter]
    refine ⟨hrow, ?_⟩
    unfold rhoWin
    have hl : 0 ≤ (1 + max (-C.aOf p X N) 0) ^ (-(1 : ℝ) / 6) := ell_nonneg' _
    nlinarith [hfold, hell, hsA, hl]
  · unfold wmCut
    nlinarith [hfold, hell, hsA]

end FoldChart

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.fold_Z_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fold_Z_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.fold_in_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fold_in_window

end FormalResearch.JacobiEigenvectors.TheoremA

end
