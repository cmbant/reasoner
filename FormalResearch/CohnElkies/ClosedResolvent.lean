module

public import FormalResearch.Special.AiryCftMittagLeffler
public import FormalResearch.Special.AiryCft2FirstDerivZero

/-!
# The closed diagonal Airy resolvent (CR.1, CR.2, CR.3 and the Riccati/derivative step)

Source: `CFT/sign_uncertainty/paper/ce_cardinal_resolvent.tex`, Theorem CR.1 (label `cecr:CR1`; equations `cecr:CR.1`, `cecr:CR.2`,
`cecr:CR.3`, and the proof's (CR.4)–(CR.6a)).

Notation (as in the note, `a_n = airyZero n`, `n ≥ 1`, indexed here by `n : ℕ` as `airyZero (n+1)`):
`m(w) = Ai'(w)/Ai(w)` (`cohnM`), `R_2(v,w) = (m(w) - m(v))/(v - w)` (`cohnR2`), `a` a real zero of `Ai'`,
`c_n = (a_n - a)⁻¹` (`cohnC`), `E_n = a_1 - a_n` (`cohnE`), `L_n(u) = Ai(u)/(u - a_n)` with its removable value
`Ai'(a_n)` at `u = a_n` (`cohnL`), `G_q(u) = Σ_n c_n² L_n(u)² / (1 + q E_n)` (`cohnG`), `z = a_1 + q⁻¹`.

**Proved, with no hypothesis beyond those displayed** (the Hadamard / Mittag-Leffler input is the library theorem
`airyAi_logDeriv_mittagLeffler_real`, `Special/AiryCftMittagLeffler`, which is proved there, so nothing is assumed):

* `cohnM_hasDerivAt`: the Riccati equation `m' = x - m²` wherever `Ai(x) ≠ 0`.
* `cohnR2_hasSum` (CR.4, off the diagonal): `Σ_n 1/((v - a_n)(w - a_n)) = R_2(v,w)` for `v ≠ w`, `Ai(v), Ai(w) ≠ 0`.
* `cohnR2_diag_hasSum` and `tendsto_cohnR2_diag`: the diagonal value `Σ_n (v - a_n)⁻² = m(v)² - v = -m'(v)` and
  `R_2(v,w) → -m'(v)` as `w → v` (the derivative step that gives the diagonal from the off-diagonal formula).
* `closedResolvent_hasSum` (**CR.2**): for a real zero `a` of `Ai'`, `q > 0`, `z = a_1 + q⁻¹ ≠ a`, and any real `u`
  with `u ≠ a`, `u ≠ z` (this contains the paper's range `u < a_1`, Airy nodes included, with `a = a_1'`), the series
  defining `G_q(u)` converges to the closed form of (CR.2).  `closedResolvent_hasSum_of_lt` is the same statement with
  exactly the paper's hypotheses (`a_1 < a = a_1'`, `u < a_1`).
* `closedResolvent_removable`: for `z = a` the closed form is undefined termwise, and the series value is the limit of
  the closed form as `z → a` (the paper's "removable limit"; the series value is continuous in `z`).
* `unweightedDiagonal_hasSum` (**CR.3**): `Σ c_n² L_n(u)² = (Ai'² - (a+u)Ai²)/(u-a)² + 2 Ai Ai'/(u-a)³` for
  `u ≠ a` (for `u` an Airy node, both sides are the single term).  The paper recalls this from O.11v(2); here it is
  proved by the same partial-fraction argument.

**Difference of route from the paper.** The paper differentiates the series `R_3(a,u,z) = Σ ∏ (· - a_n)⁻¹` once in `a`
and once in `u` (CR.5a) and then differentiates the closed form of `R_3` using the Riccati equation (CR.6a).  Here the
summand `(a - a_n)⁻² (u - a_n)⁻² (z - a_n)⁻¹` is decomposed into partial fractions in `a_n` (an identity of rational
functions, checked by `field_simp; ring`), and the two kinds of resulting sums are the library's Mittag-Leffler
differences `Σ [(w - a_n)⁻¹ - (z - a_n)⁻¹] = m(w) - m(z)` and sum rule `Σ (w - a_n)⁻² = m(w)² - w`; no termwise
differentiation of a series is needed.  The Riccati equation is used (in sum-rule form) for exactly the same purpose as
in the paper, and `cohnM_hasDerivAt` proves it separately in derivative form.  The mixed derivative of the closed form
of `R_3` itself (CR.6, CR.6a as a statement about `∂_a ∂_u`) is not stated.

**Differences in generality.** The paper fixes `a = a_1'` (the largest zero of `Ai'`); the theorems here allow any
real zero `a` of `Ai'` (then `Ai(a) ≠ 0` by the Wronskian), which includes the paper's case.  `u` is not restricted to
`u < a_1`: any real `u ∉ {a, z}` is allowed. The Stieltjes-measure and asymptotic follow-ons CR.2–CR.4 live in
`FormalResearch.CohnElkies.StieltjesMixture` and `FormalResearch.CohnElkies.CardinalAsymptotics`.
-/

@[expose] public section

open Filter Topology Set
open FormalResearch.Special

namespace FormalResearch.CohnElkies

/-- `m(w) = Ai'(w)/Ai(w)`. -/
noncomputable def cohnM (x : ℝ) : ℝ := airyAi' x / airyAi x

/-- `R_2(v,w) = (m(w) - m(v))/(v - w)` (CR.4), off the diagonal. -/
noncomputable def cohnR2 (v w : ℝ) : ℝ := (cohnM w - cohnM v) / (v - w)

/-- `c_n = (a_n - a)⁻¹`, with `a_n = airyZero (n+1)`. -/
noncomputable def cohnC (a : ℝ) (n : ℕ) : ℝ := (airyZero (n + 1) - a)⁻¹

/-- `E_n = a_1 - a_n`. -/
noncomputable def cohnE (n : ℕ) : ℝ := airyZero 1 - airyZero (n + 1)

/-- `L_n(u) = Ai(u)/(u - a_n)`, with the removable value `Ai'(a_n)` at `u = a_n`. -/
noncomputable def cohnL (n : ℕ) (u : ℝ) : ℝ :=
  if u = airyZero (n + 1) then airyAi' (airyZero (n + 1)) else airyAi u / (u - airyZero (n + 1))

/-- `G_q(u) = Σ_n c_n² L_n(u)² / (1 + q E_n)` (CR.1). -/
noncomputable def cohnG (a q u : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + q * cohnE n)

/-! ### Elementary facts -/

lemma airyAi_ne_zero_of_gt {z : ℝ} (h : airyZero 1 < z) : airyAi z ≠ 0 := by
  intro h0
  by_cases hz : z ≤ 0
  · obtain ⟨n, hn, rfl⟩ := exists_airyZero_eq h0 hz
    exact absurd (airyZero_anti (le_refl 1) hn) (not_le.mpr h)
  · exact (airyAi_pos (not_le.mp hz).le).ne' h0

lemma sub_airyZero_ne_zero {v : ℝ} (hv : airyAi v ≠ 0) (n : ℕ) : v - airyZero (n + 1) ≠ 0 := by
  intro h
  have : v = airyZero (n + 1) := by linarith
  exact hv (this ▸ airyAi_airyZero _)

/-! ### The Riccati equation -/

/-- **Riccati equation** `m' = x - m²` for `m = Ai'/Ai`, wherever `Ai(x) ≠ 0`. -/
theorem cohnM_hasDerivAt {x : ℝ} (hx : airyAi x ≠ 0) :
    HasDerivAt cohnM (x - cohnM x ^ 2) x := by
  have h := (hasDerivAt_airyAi' x).div (hasDerivAt_airyAi x) hx
  unfold cohnM
  convert h using 1
  field_simp

/-! ### The Mittag-Leffler input in the forms used -/

lemma hasSum_inv_sub_diff {w z : ℝ} (hw : airyAi w ≠ 0) (hz : airyAi z ≠ 0) :
    HasSum (fun n : ℕ => 1 / (w - airyZero (n + 1)) - 1 / (z - airyZero (n + 1)))
      (cohnM w - cohnM z) := by
  have h := (airyAi_logDeriv_mittagLeffler_real hw).sub (airyAi_logDeriv_mittagLeffler_real hz)
  convert h using 1
  · funext n; ring
  · simp only [cohnM]; ring

lemma hasSum_inv_sq (w : ℝ) (hw : airyAi w ≠ 0) :
    HasSum (fun n : ℕ => ((w - airyZero (n + 1)) ^ 2)⁻¹) (cohnM w ^ 2 - w) :=
  airyAi_sq_series_real hw

/-- **CR.4 (off the diagonal)**: `Σ_n 1/((v - a_n)(w - a_n)) = (m(w) - m(v))/(v - w)`. -/
theorem cohnR2_hasSum {v w : ℝ} (hv : airyAi v ≠ 0) (hw : airyAi w ≠ 0) (hvw : v ≠ w) :
    HasSum (fun n : ℕ => 1 / ((v - airyZero (n + 1)) * (w - airyZero (n + 1)))) (cohnR2 v w) := by
  have hvw' : v - w ≠ 0 := sub_ne_zero.mpr hvw
  have h := (hasSum_inv_sub_diff hw hv).div_const (v - w)
  convert h using 1
  · funext n
    have h1 := sub_airyZero_ne_zero hv n
    have h2 := sub_airyZero_ne_zero hw n
    field_simp
    ring
  · rfl

/-- The diagonal value of `R_2`: `Σ_n (v - a_n)⁻² = m(v)² - v = -m'(v)` (Riccati). -/
theorem cohnR2_diag_hasSum {v : ℝ} (hv : airyAi v ≠ 0) :
    HasSum (fun n : ℕ => 1 / ((v - airyZero (n + 1)) * (v - airyZero (n + 1))))
      (-(v - cohnM v ^ 2)) := by
  have h := hasSum_inv_sq v hv
  convert h using 1
  · funext n; rw [← sq, one_div]
  · ring

/-- **The derivative step**: `R_2(v,w) → -m'(v) = m(v)² - v` as `w → v`. -/
theorem tendsto_cohnR2_diag {v : ℝ} (hv : airyAi v ≠ 0) :
    Tendsto (cohnR2 v) (𝓝[≠] v) (𝓝 (-(v - cohnM v ^ 2))) := by
  have h := (cohnM_hasDerivAt hv).tendsto_slope
  have h2 := h.neg
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w - v ≠ 0 := sub_ne_zero.mpr hw
  have hvw : v - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  simp only [slope_def_field, cohnR2]
  have : v - w = -(w - v) := by ring
  rw [this, div_neg]

/-! ### The partial-fraction sums -/

/-- The sum `Σ_n (a - a_n)⁻² (u - a_n)⁻² (z - a_n)⁻¹` in terms of `m(a), m(u), m(z)` (partial fractions). -/
lemma hasSum_cubic {a u z : ℝ} (ha : airyAi a ≠ 0) (hu : airyAi u ≠ 0) (hz : airyAi z ≠ 0)
    (hau : a ≠ u) (haz : a ≠ z) (huz : u ≠ z) :
    HasSum (fun n : ℕ => 1 / ((a - airyZero (n + 1)) ^ 2 * (u - airyZero (n + 1)) ^ 2 *
        (z - airyZero (n + 1))))
      (1 / ((u - a) ^ 2 * (z - a)) * (cohnM a ^ 2 - a)
        + 1 / ((u - a) ^ 2 * (z - u)) * (cohnM u ^ 2 - u)
        + (3 * a - u - 2 * z) / ((u - a) ^ 3 * (z - a) ^ 2) * (cohnM a - cohnM z)
        + (a - 3 * u + 2 * z) / ((u - a) ^ 3 * (z - u) ^ 2) * (cohnM u - cohnM z)) := by
  have hsa := ((hasSum_inv_sq a ha).mul_left (1 / ((u - a) ^ 2 * (z - a))))
  have hsu := ((hasSum_inv_sq u hu).mul_left (1 / ((u - a) ^ 2 * (z - u))))
  have hda := (hasSum_inv_sub_diff ha hz).mul_left ((3 * a - u - 2 * z) / ((u - a) ^ 3 * (z - a) ^ 2))
  have hdu := (hasSum_inv_sub_diff hu hz).mul_left ((a - 3 * u + 2 * z) / ((u - a) ^ 3 * (z - u) ^ 2))
  have h := ((hsa.add hsu).add hda).add hdu
  convert h using 1
  funext n
  have h1 := sub_airyZero_ne_zero ha n
  have h2 := sub_airyZero_ne_zero hu n
  have h3 := sub_airyZero_ne_zero hz n
  have e1 : u - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hau)
  have e2 : z - a ≠ 0 := sub_ne_zero.mpr (Ne.symm haz)
  have e3 : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
  field_simp
  ring

/-- The unweighted version `Σ_n (a - a_n)⁻² (u - a_n)⁻²`. -/
lemma hasSum_quartic {a u : ℝ} (ha : airyAi a ≠ 0) (hu : airyAi u ≠ 0) (hau : a ≠ u) :
    HasSum (fun n : ℕ => 1 / ((a - airyZero (n + 1)) ^ 2 * (u - airyZero (n + 1)) ^ 2))
      (((cohnM a ^ 2 - a) + (cohnM u ^ 2 - u)) / (u - a) ^ 2
        + 2 * (cohnM u - cohnM a) / (u - a) ^ 3) := by
  have hsa := hasSum_inv_sq a ha
  have hsu := hasSum_inv_sq u hu
  have hd := (hasSum_inv_sub_diff hu ha).mul_left (2 / (u - a) ^ 3)
  have h := ((hsa.add hsu).div_const ((u - a) ^ 2)).add hd
  convert h using 1
  · funext n
    have h1 := sub_airyZero_ne_zero ha n
    have h2 := sub_airyZero_ne_zero hu n
    have e1 : u - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hau)
    field_simp
    ring
  · field_simp

/-! ### CR.2 and CR.3 -/

/-- The closed form on the right of (CR.2) (with the factor `q⁻¹` and `z = a_1 + q⁻¹`). -/
noncomputable def closedResolventRHS (a q u : ℝ) : ℝ :=
  let z := airyZero 1 + q⁻¹
  q⁻¹ * ((cohnM z / ((z - a) ^ 2 * (z - u) ^ 2)
          + (2 * a * u - a * z - u * z) / ((u - a) ^ 2 * (z - a) * (z - u))) * airyAi u ^ 2
        + (a - 3 * u + 2 * z) / ((u - a) ^ 3 * (z - u) ^ 2) * (airyAi u * airyAi' u)
        + 1 / ((u - a) ^ 2 * (z - u)) * airyAi' u ^ 2)

lemma cohnL_self (n : ℕ) : cohnL n (airyZero (n + 1)) = airyAi' (airyZero (n + 1)) := by
  simp [cohnL]

lemma cohnL_of_ne {n : ℕ} {u : ℝ} (h : u ≠ airyZero (n + 1)) :
    cohnL n u = airyAi u / (u - airyZero (n + 1)) := by
  simp [cohnL, h]

/-- **Theorem CR.1 / eq. (CR.2)**: closed form of the diagonal resolvent `G_q(u)`.

For a real zero `a` of `Ai'` (the paper: `a = a_1'`), `q > 0`, `z = a_1 + q⁻¹ ≠ a`, and real `u ∉ {a, z}` (in
particular every `u < a_1` when `a_1 < a`; Airy nodes `u = a_n` are included): the series
`Σ_n c_n² L_n(u)² / (1 + q E_n)` converges to
`q⁻¹ [ { m(z)/((z-a)²(z-u)²) + (2au - az - uz)/((u-a)²(z-a)(z-u)) } Ai(u)²
      + (a - 3u + 2z)/((u-a)³(z-u)²) Ai(u) Ai'(u) + Ai'(u)²/((u-a)²(z-u)) ]`. -/
theorem closedResolvent_hasSum {a q u : ℝ} (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ ≠ a) (hua : u ≠ a) (huz : u ≠ airyZero 1 + q⁻¹) :
    HasSum (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + q * cohnE n))
      (closedResolventRHS a q u) := by
  set z : ℝ := airyZero 1 + q⁻¹ with hzdef
  have hzgt : airyZero 1 < z := by
    have : 0 < q⁻¹ := inv_pos.mpr hq
    linarith
  have hAz : airyAi z ≠ 0 := airyAi_ne_zero_of_gt hzgt
  have hAa : airyAi a ≠ 0 := airyAi_ne_zero_of_deriv_zero ha
  have hma : cohnM a = 0 := by simp [cohnM, ha]
  have hq0 : q ≠ 0 := hq.ne'
  -- the denominators
  have hden : ∀ n : ℕ, 1 + q * cohnE n = q * (z - airyZero (n + 1)) := by
    intro n
    simp only [cohnE, hzdef]
    field_simp
    ring
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hzu' : z - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huz)
  have hua' : u - a ≠ 0 := sub_ne_zero.mpr hua
  by_cases hAu : airyAi u = 0
  · -- Airy node: a single term
    obtain ⟨k, hk, hku⟩ : ∃ k : ℕ, 1 ≤ k ∧ u = airyZero k := by
      by_cases hu0 : u ≤ 0
      · exact exists_airyZero_eq hAu hu0
      · exact absurd hAu (airyAi_pos (not_le.mp hu0).le).ne'
    obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, k = n0 + 1 := ⟨k - 1, by omega⟩
    have hsingle := hasSum_single (f := fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + q * cohnE n))
      n0 (fun n hn => by
        have hne : u ≠ airyZero (n + 1) := by
          intro h
          apply hn
          have hinj : n + 1 = n0 + 1 := by
            have h1 : airyZero (n + 1) = airyZero (n0 + 1) := h.symm.trans hku
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact absurd h1 (airyZero_lt_of_lt (by omega) hlt).ne'
            · exact absurd h1 (airyZero_lt_of_lt (by omega) hgt).ne
          omega
        rw [cohnL_of_ne hne, hAu]
        simp)
    convert hsingle using 1
    simp only [closedResolventRHS]
    rw [show cohnL n0 u = airyAi' (airyZero (n0 + 1)) by rw [hku]; exact cohnL_self n0, hden, cohnC, ← hzdef, hAu, ← hku]
    field_simp
    ring
  · -- generic point
    have hmain := hasSum_cubic hAa hAu hAz (Ne.symm hua) (fun h => hza h.symm) huz
    have hmain' := hmain.mul_left (airyAi u ^ 2 / q)
    convert hmain' using 1
    · funext n
      have hne : u ≠ airyZero (n + 1) := fun h => hAu (h ▸ airyAi_airyZero _)
      have h1 := sub_airyZero_ne_zero hAa n
      have h2 := sub_airyZero_ne_zero hAu n
      have h3 := sub_airyZero_ne_zero hAz n
      rw [cohnL_of_ne hne, hden, cohnC]
      have e : airyZero (n + 1) - a = -(a - airyZero (n + 1)) := by ring
      rw [e]
      field_simp
    · simp only [closedResolventRHS, hma]
      have hmu : airyAi' u = cohnM u * airyAi u := by simp [cohnM]; field_simp
      rw [← hzdef]
      rw [hmu]
      simp only [cohnM]
      field_simp
      ring

/-- `G_q(u)` as a `tsum`: `cohnG a q u = closedResolventRHS a q u`. -/
theorem cohnG_eq {a q u : ℝ} (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ ≠ a) (hua : u ≠ a) (huz : u ≠ airyZero 1 + q⁻¹) :
    cohnG a q u = closedResolventRHS a q u :=
  (closedResolvent_hasSum ha hq hza hua huz).tsum_eq

/-- Theorem CR.1 with exactly the paper's hypotheses: `a = a_1'` the largest zero of `Ai'`, `q > 0`, `z ≠ a`,
`u < a_1`. -/
theorem closedResolvent_hasSum_of_lt {a q u : ℝ} (ha1 : airyZero 1 < a) (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ ≠ a) (hu : u < airyZero 1) :
    HasSum (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2 / (1 + q * cohnE n))
      (closedResolventRHS a q u) := by
  have : 0 < q⁻¹ := inv_pos.mpr hq
  exact closedResolvent_hasSum ha hq hza (by linarith) (by linarith)

/-- **Equation (CR.3)**: the unweighted diagonal `Σ_n c_n² L_n(u)²` for a real zero `a` of `Ai'` and `u ≠ a`. -/
theorem unweightedDiagonal_hasSum {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) :
    HasSum (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2)
      ((airyAi' u ^ 2 - (a + u) * airyAi u ^ 2) / (u - a) ^ 2
        + 2 * airyAi u * airyAi' u / (u - a) ^ 3) := by
  have hAa : airyAi a ≠ 0 := airyAi_ne_zero_of_deriv_zero ha
  have hma : cohnM a = 0 := by simp [cohnM, ha]
  have hua' : u - a ≠ 0 := sub_ne_zero.mpr hua
  by_cases hAu : airyAi u = 0
  · obtain ⟨k, hk, hku⟩ : ∃ k : ℕ, 1 ≤ k ∧ u = airyZero k := by
      by_cases hu0 : u ≤ 0
      · exact exists_airyZero_eq hAu hu0
      · exact absurd hAu (airyAi_pos (not_le.mp hu0).le).ne'
    obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, k = n0 + 1 := ⟨k - 1, by omega⟩
    have hsingle := hasSum_single (f := fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2)
      n0 (fun n hn => by
        have hne : u ≠ airyZero (n + 1) := by
          intro h
          apply hn
          have hinj : n + 1 = n0 + 1 := by
            have h1 : airyZero (n + 1) = airyZero (n0 + 1) := h.symm.trans hku
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact absurd h1 (airyZero_lt_of_lt (by omega) hlt).ne'
            · exact absurd h1 (airyZero_lt_of_lt (by omega) hgt).ne
          omega
        rw [cohnL_of_ne hne, hAu]
        simp)
    convert hsingle using 1
    rw [show cohnL n0 u = airyAi' (airyZero (n0 + 1)) by rw [hku]; exact cohnL_self n0, cohnC, ← hku, hAu]
    field_simp
    ring
  · have hmain := hasSum_quartic hAa hAu (Ne.symm hua)
    have hmain' := hmain.mul_left (airyAi u ^ 2)
    convert hmain' using 1
    · funext n
      have hne : u ≠ airyZero (n + 1) := fun h => hAu (h ▸ airyAi_airyZero _)
      have h1 := sub_airyZero_ne_zero hAa n
      have h2 := sub_airyZero_ne_zero hAu n
      rw [cohnL_of_ne hne, cohnC]
      have e : airyZero (n + 1) - a = -(a - airyZero (n + 1)) := by ring
      rw [e]
      field_simp
    · have hmu : airyAi' u = cohnM u * airyAi u := by simp [cohnM]; field_simp
      rw [hma, hmu]
      simp only [cohnM]
      field_simp
      ring

/-! ### The case `z = a` (removable limit) -/

/-- Continuity in `z` of the series `Σ_n c_n² L_n(u)² / (z - a_n)` on `z > a_1`. -/
lemma continuousOn_series_z {a u : ℝ} (ha : airyAi' a = 0) (hua : u ≠ a) :
    ContinuousOn (fun z : ℝ => ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 / (z - airyZero (n + 1)))
      (Ioi (airyZero 1)) := by
  intro z0 hz0
  have hz0' : airyZero 1 < z0 := hz0
  -- dominate on `z ≥ ζ` for a fixed ζ ∈ (a_1, z0) by the (summable) terms at `ζ`
  set ζ : ℝ := (airyZero 1 + z0) / 2 with hζ
  have hζ1 : airyZero 1 < ζ := by rw [hζ]; linarith
  have hζ2 : ζ < z0 := by rw [hζ]; linarith
  have hsum : Summable (fun n : ℕ => cohnC a n ^ 2 * cohnL n u ^ 2) :=
    (unweightedDiagonal_hasSum ha hua).summable
  have hbound : ∀ n : ℕ, ∀ z ∈ Ici ζ,
      ‖cohnC a n ^ 2 * cohnL n u ^ 2 / (z - airyZero (n + 1))‖
        ≤ (ζ - airyZero 1)⁻¹ * (cohnC a n ^ 2 * cohnL n u ^ 2) := by
    intro n z hz
    have hz' : ζ ≤ z := hz
    have hn : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti (le_refl 1) (by omega)
    have hpos : 0 < ζ - airyZero 1 := by linarith
    have hpos2 : 0 < z - airyZero (n + 1) := by linarith
    have hnn : 0 ≤ cohnC a n ^ 2 * cohnL n u ^ 2 := by positivity
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_of_pos hpos2,
      div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_right _ hnn
    exact inv_anti₀ hpos (by linarith)
  have hcont : ContinuousOn
      (fun z : ℝ => ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 / (z - airyZero (n + 1))) (Ici ζ) := by
    refine continuousOn_tsum (u := fun n => (ζ - airyZero 1)⁻¹ * (cohnC a n ^ 2 * cohnL n u ^ 2))
      (fun n => ?_) (hsum.mul_left _) hbound
    refine ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const) ?_
    intro z hz
    have hz' : ζ ≤ z := hz
    have hn : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti (le_refl 1) (by omega)
    linarith
  exact (hcont.continuousAt (Ici_mem_nhds hζ2)).continuousWithinAt

/-- **The case `z = a` of (CR.2)** (the "removable limit"): if `a_1 + q⁻¹ = a` then `G_q(u)` is the limit, as
`z' → a`, `z' ≠ a`, of the closed form of (CR.2) evaluated at `q' = (z' - a_1)⁻¹`. -/
theorem closedResolvent_removable {a q u : ℝ} (ha : airyAi' a = 0) (hq : 0 < q)
    (hza : airyZero 1 + q⁻¹ = a) (hua : u ≠ a) :
    Tendsto (fun z' : ℝ => closedResolventRHS a (z' - airyZero 1)⁻¹ u) (𝓝[≠] a)
      (𝓝 (cohnG a q u)) := by
  have hqz : q⁻¹ = a - airyZero 1 := by linarith
  have hgt : airyZero 1 < a := by
    have : 0 < q⁻¹ := inv_pos.mpr hq
    linarith
  -- the series value as a function of `z'`
  set S : ℝ → ℝ := fun z => ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 / (z - airyZero (n + 1)) with hS
  have hSc : ContinuousAt S a := (continuousOn_series_z ha hua).continuousAt (Ioi_mem_nhds hgt)
  have hGS : ∀ z : ℝ, airyZero 1 < z → ∑' n : ℕ, cohnC a n ^ 2 * cohnL n u ^ 2 /
      (1 + (z - airyZero 1)⁻¹ * cohnE n) = (z - airyZero 1) * S z := by
    intro z hz
    rw [hS, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    have hn : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti (le_refl 1) (by omega)
    have h1 : z - airyZero 1 ≠ 0 := by linarith
    have h2 : z - airyZero (n + 1) ≠ 0 := by linarith
    have : 1 + (z - airyZero 1)⁻¹ * cohnE n = (z - airyZero 1)⁻¹ * (z - airyZero (n + 1)) := by
      simp only [cohnE]; field_simp; ring
    rw [this]
    have h3 : (z - airyZero 1)⁻¹ ≠ 0 := inv_ne_zero h1
    field_simp
  have hq' : q = (a - airyZero 1)⁻¹ := by rw [← hqz, inv_inv]
  have hGval : cohnG a q u = (a - airyZero 1) * S a := by
    have := hGS a hgt
    unfold cohnG
    rw [hq']; exact this
  have hlim : Tendsto (fun z' : ℝ => (z' - airyZero 1) * S z') (𝓝 a) (𝓝 ((a - airyZero 1) * S a)) := by
    refine Tendsto.mul ?_ hSc.tendsto
    exact (continuousAt_id.sub continuousAt_const).tendsto
  rw [hGval]
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ z' in 𝓝[≠] a, airyZero 1 < z' ∧ z' ≠ a ∧ z' ≠ u := by
    have h1 : ∀ᶠ z' in 𝓝[≠] a, airyZero 1 < z' :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hgt)
    have h2 : ∀ᶠ z' in 𝓝[≠] a, z' ≠ a := self_mem_nhdsWithin
    have h3 : ∀ᶠ z' in 𝓝[≠] a, z' ≠ u :=
      nhdsWithin_le_nhds ((isOpen_ne.mem_nhds (Ne.symm hua)))
    exact h1.and (h2.and h3)
  filter_upwards [hev] with z' ⟨hz1, hz2, hz3⟩
  have hq' : 0 < (z' - airyZero 1)⁻¹ := inv_pos.mpr (by linarith)
  have hz'' : airyZero 1 + ((z' - airyZero 1)⁻¹)⁻¹ = z' := by rw [inv_inv]; ring
  have key := cohnG_eq (a := a) (q := (z' - airyZero 1)⁻¹) (u := u) ha hq'
    (by rw [hz'']; exact hz2) hua (by rw [hz'']; exact fun h => hz3 h.symm)
  rw [← key]
  unfold cohnG
  exact (hGS z' hz1).symm

/-! ### Axioms -/

/-- info: 'FormalResearch.CohnElkies.cohnM_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnM_hasDerivAt

/-- info: 'FormalResearch.CohnElkies.cohnR2_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.cohnR2_hasSum

/-- info: 'FormalResearch.CohnElkies.tendsto_cohnR2_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.tendsto_cohnR2_diag

/-- info: 'FormalResearch.CohnElkies.closedResolvent_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.closedResolvent_hasSum

/-- info: 'FormalResearch.CohnElkies.closedResolvent_removable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.closedResolvent_removable

/-- info: 'FormalResearch.CohnElkies.unweightedDiagonal_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.unweightedDiagonal_hasSum

end FormalResearch.CohnElkies
