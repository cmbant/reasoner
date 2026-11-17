module

public import FormalResearch.Special.BulkKappaExplicit
public import FormalResearch.Special.DiscreteLgZeros

/-!
# Bulk zero localisation for the physical chains

`bk_zeros_of_out`: for a family `Fam` as in `bk_sharp_abs(H)` and every compact `[a, b] ⊂ (0, q_*)` there are `ε₀, C₀ > 0` such that for every member with `h ≤ ε₀` and every bond `(k, k+1)` with
`q_k, q_{k+1} ∈ [a, b]` across which the chain changes sign (`Y_k Y_{k+1} ≤ 0`) there is an integer `m` with

`Φ(q_{k+1})/h - C₀ h ≤ π (m - 1/4) ≤ Φ(q_k)/h + C₀ h`,   `Φ(q) = ∫_q^{q_*} arccos u` (`bkPhase`),

i.e. the bond contains, up to `O(h)` in the phase, a point of the Bohr-Sommerfeld lattice `Φ(q) = π h (m - 1/4)` (zeros `(2j+1)π/2` of `cos(Θ(q)/h - Θ_*/h + π/4)`).  The proof composes the bulk form `BkBulkAt`
of the Airy window (with `κ² δ ≥ 1` from the sharp amplitude, and `|μ| ≤ δ³`) with `dlg_zero_localisation` (`DiscreteLgZeros`): `κ cos χ + μ sin χ = s (|κ|/cos φ) cos(χ - φ)`, `φ = arctan(sμ/|κ|) = O(δ^{7/2})`,
and the relative bulk error is `O(h)`; so the localisation is `O(h)` although `κ² δ → 2` is only `o(1)` (only the lower bound `|κ| ≥ δ^{-1/2}` is used).

**Claim class: proved.**  **Not formalised:** the converse (every Bohr-Sommerfeld point produces a sign change, hence the count of sign changes / the Weyl-law count of the bulk zeros), the conversion of the phase window
into a window in `q` (needs `arccos u ≥ θ_min > 0` on `[a, b]`), uniformity of `ε₀, C₀` in `(a, b)` and in the data, the end regions (`q → 0`, `q → q_*`).
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- The phase integral is non-increasing: `Φ(q') ≤ Φ(q)` for `0 ≤ q ≤ q' ≤ q_*`. -/
lemma bk_phase_anti {P Q τ x qs q q' : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hq : 0 ≤ q) (hqq : q ≤ q') (hq' : q' ≤ qs) : bkPhase P Q τ x qs q' ≤ bkPhase P Q τ x qs q := by
  have hcont := bk_cont (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (c1 := q) hP hQ hα hβ hq
  have i1 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume q q' :=
    (hcont.mono (by rw [Set.uIcc_of_le hqq]; exact Set.Icc_subset_Icc le_rfl hq')).intervalIntegrable
  have i2 : IntervalIntegrable (fun s => Real.arccos (hrU P Q τ x s)) MeasureTheory.volume q' qs :=
    (hcont.mono (by rw [Set.uIcc_of_le hq']; exact Set.Icc_subset_Icc hqq le_rfl)).intervalIntegrable
  unfold bkPhase
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have : 0 ≤ ∫ s in q..q', Real.arccos (hrU P Q τ x s) :=
    intervalIntegral.integral_nonneg hqq (fun s _ => Real.arccos_nonneg (hrU P Q τ x s))
  linarith

lemma bk_polar (s a μ χ φ : ℝ) (hs1 : s ^ 2 = 1) (ha : a ≠ 0) (hc : Real.cos φ ≠ 0)
    (htan : Real.sin φ = (s * μ / a) * Real.cos φ) :
    s * a * Real.cos χ + μ * Real.sin χ = s * (a / Real.cos φ) * Real.cos (χ - φ) := by
  rw [Real.cos_sub, htan]
  field_simp
  linear_combination (μ * Real.sin χ) * (-hs1)

/-- **The algebra of the zero localisation** (see the module docstring). -/
lemma bk_zero_alg {Y0 Y1 ρ δ W0 W1 κ μ χ0 χ1 C : ℝ} (hρ : 0 < ρ) (hW0 : 0 < W0) (hW1 : 0 < W1) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hκ : 0 < |κ|) (hμκ : |μ| ≤ |κ|) (hχ : χ0 ≤ χ1) (s : ℝ) (hs : s = 1 ∨ s = -1) (hκs : κ = s * |κ|) (hch : Y0 * Y1 ≤ 0)
    (hb0 : |Y0 - ρ * (1 / √π) * W0 * (κ * Real.cos χ0 + μ * Real.sin χ0)| ≤ C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W0)
    (hb1 : |Y1 - ρ * (1 / √π) * W1 * (κ * Real.cos χ1 + μ * Real.sin χ1)| ≤ C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W1) :
    ∃ j : ℤ, χ0 - (|μ| / |κ| + π / 2 * (2 * C * √π * δ ^ 3)) ≤ (2 * j + 1) * π / 2 ∧
      (2 * j + 1) * π / 2 ≤ χ1 + (|μ| / |κ| + π / 2 * (2 * C * √π * δ ^ 3)) := by
  have hR : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hs1 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  set φ : ℝ := Real.arctan (s * μ / |κ|) with hφ
  have hc : 0 < Real.cos φ := Real.cos_arctan_pos _
  have hc1 : Real.cos φ ≤ 1 := Real.cos_le_one _
  have htan : Real.sin φ = (s * μ / |κ|) * Real.cos φ := by
    have := Real.tan_arctan (s * μ / |κ|)
    rw [Real.tan_eq_sin_div_cos] at this
    rw [← hφ] at this
    field_simp at this ⊢
    linarith
  have hφabs : |φ| ≤ |μ| / |κ| := by
    have hy : abs ((s * μ) / |κ|) = |μ| / |κ| := by
      rw [abs_div, abs_mul, abs_of_pos hκ]
      have : |s| = 1 := by rcases hs with rfl | rfl <;> simp
      rw [this, one_mul]
    rw [← hy]
    rcases le_total 0 (s * μ / |κ|) with h0 | h0
    · rw [abs_of_nonneg h0, hφ, abs_of_nonneg (Real.arctan_nonneg.2 h0)]
      exact Real.arctan_le_self h0
    · rw [abs_of_nonpos h0, hφ, abs_of_nonpos (Real.arctan_le_zero.2 h0)]
      have := Real.self_le_arctan h0
      linarith
  -- the amplitude `R`
  set R : ℝ := ρ * (1 / √π) * (|κ| / Real.cos φ) with hRdef
  have hR0 : 0 < R := by positivity
  have hid : ∀ χ : ℝ, κ * Real.cos χ + μ * Real.sin χ = s * (|κ| / Real.cos φ) * Real.cos (χ - φ) := by
    intro χ
    have h1 := bk_polar s |κ| μ χ φ hs1 hκ.ne' hc.ne' htan
    have h2 : s * |κ| * Real.cos χ = κ * Real.cos χ := by rw [← hκs]
    rw [h2] at h1
    exact h1
  set ε : ℝ := 2 * C * √π * δ ^ 3 with hε
  have hε0 : 0 ≤ ε := by positivity
  have hbd : ∀ (Y W χ : ℝ), 0 < W → |Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)| ≤ C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W →
      |s * Y - R * W * Real.cos (χ - φ)| ≤ ε * (R * W) := by
    intro Y W χ hW hb
    have e : s * Y - R * W * Real.cos (χ - φ) = s * (Y - ρ * (1 / √π) * W * (κ * Real.cos χ + μ * Real.sin χ)) := by
      rw [hid χ, hRdef]
      have : s * s = 1 := by nlinarith [hs1]
      linear_combination (ρ * (1 / √π) * W * (|κ| / Real.cos φ) * Real.cos (χ - φ)) * this
    rw [e, abs_mul]
    have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hsabs, one_mul]
    refine hb.trans ?_
    -- `C (|κ|+|μ|) ρ δ³ W ≤ ε R W`
    have h1 : (|κ| + |μ|) * (ρ * δ ^ 3) ≤ (2 * |κ|) * (ρ * δ ^ 3) := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : ε * R = 2 * C * δ ^ 3 * ρ * |κ| * (√π * (1 / √π)) / Real.cos φ := by
      rw [hε, hRdef]; field_simp
    have h3 : √π * (1 / √π) = 1 := by field_simp
    have h4 : 2 * C * δ ^ 3 * ρ * |κ| ≤ ε * R := by
      rw [h2, h3, mul_one]
      rw [le_div_iff₀ hc]
      have : 0 ≤ 2 * C * δ ^ 3 * ρ * |κ| := by positivity
      nlinarith
    calc C * ((|κ| + |μ|) * (ρ * δ ^ 3)) * W ≤ C * ((2 * |κ|) * (ρ * δ ^ 3)) * W :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) hW.le
      _ = (2 * C * δ ^ 3 * ρ * |κ|) * W := by ring
      _ ≤ (ε * R) * W := mul_le_mul_of_nonneg_right h4 hW.le
      _ = ε * (R * W) := by ring
  have hloc := dlg_zero_localisation (Y0 := s * Y0) (Y1 := s * Y1) (R := R) (w0 := W0) (w1 := W1) (x0 := χ0 - φ) (x1 := χ1 - φ) (ε := ε)
    (mul_pos hR0 hW0) (mul_pos hR0 hW1) hε0 (hbd Y0 W0 χ0 hW0 hb0) (hbd Y1 W1 χ1 hW1 hb1)
    (by nlinarith [hs1, hch]) (by linarith)
  obtain ⟨j, hj1, hj2⟩ := hloc
  have hφ' := abs_le.1 hφabs
  exact ⟨j, by linarith [hφ'.1, hφ'.2], by linarith [hφ'.1, hφ'.2]⟩

/-- The bulk phase of the window: `χ_k = Θ(q_k)/h - Θ_*/h + π/4 = π/4 - Φ(q_k)/h`. -/
lemma bk_chi_eq {P Q τ x qs c1 q0 δ q : ℝ} {k : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    (hc1 : 0 ≤ c1) (hq1 : c1 ≤ q) (hqq : q ≤ qs) (hqd : dlgQ q0 (δ ^ 3) k = q) :
    dlgP (dlgsPhase (hrU P Q τ x) c1) q0 (δ ^ 3) k - (∫ s in c1..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4 =
      π / 4 - bkPhase P Q τ x qs q / δ ^ 3 := by
  have h1 : dlgP (dlgsPhase (hrU P Q τ x) c1) q0 (δ ^ 3) k - (∫ s in c1..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 =
      -(bkPhase P Q τ x qs q / δ ^ 3) := by
    unfold dlgP
    rw [hqd, ← sub_div, bk_phase_sub (bk_cont hP hQ hα hβ hc1) hq1 hqq]
    ring
  rw [h1]; ring

/-- **Bulk zero localisation, abstract form** (see the module docstring). -/
theorem bk_zeros_of_out {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    {θ : ℝ} {q₀ : ℝ → ℝ} (hq₀ : ∀ δ : ℝ, ∀ k : ℤ, dlgQ (q₀ δ) (δ ^ 3) k = ((k : ℝ) + θ) * δ ^ 3)
    {Fam : ℝ → (ℤ → ℝ) → ℝ → Prop} {r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ} (hr : 0 < r) (hrq4 : r ≤ qs / 4) (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0)
    (Hout : BkOut θ q₀ P Q τ x qs Fam r Cmu ξ0 gmax gmin c1 c2 CA δA) (hδA : 0 < δA) :
    ∀ a b : ℝ, 0 < a → a < b → b < qs → ∃ ε C0 : ℝ, 0 < ε ∧ 0 < C0 ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε →
      ∀ k : ℤ, a ≤ ((k : ℝ) + θ) * h → ((k : ℝ) + 1 + θ) * h ≤ b → Y k * Y (k + 1) ≤ 0 →
        ∃ m : ℤ, bkPhase P Q τ x qs (((k : ℝ) + 1 + θ) * h) / h - C0 * h ≤ π * ((m : ℝ) - 1 / 4) ∧
          π * ((m : ℝ) - 1 / 4) ≤ bkPhase P Q τ x qs (((k : ℝ) + θ) * h) / h + C0 * h := by
  obtain ⟨Hwin, Hsharp, Hbulk⟩ := Hout
  intro a b ha hab hbq
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  set cs : ℝ := 1 / Real.sqrt (rkS P Q x) + 1 with hcs
  have hcs0 : 0 ≤ cs := by positivity
  set c : ℝ := min a (qs / 2) with hcdef
  have hc0 : 0 < c := lt_min ha (by positivity)
  have hca : c ≤ a := min_le_left _ _
  have hcq : c ≤ qs / 2 := min_le_right _ _
  set η : ℝ := min (qs - b) (r / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηb : η ≤ qs - b := min_le_left _ _
  have hηr : η ≤ r / 2 := min_le_right _ _
  obtain ⟨δ0, C, hδ0, hC, HB⟩ := Hbulk (c / 2) (by positivity) (by linarith) η hη hηr c (by linarith) (by linarith)
  obtain ⟨ε1, hε1, HS⟩ := Hsharp 1 one_pos
  set ε : ℝ := min ε1 (min (δ0 ^ 3) (min (δA ^ 3) (min ((ξ0 / 14) ^ 3) (min ((ξ0 ^ 3 / (48 * (Cmu * cs + 1))) ^ 3) 1)))) with hεdef
  have hεp : 0 < ε := lt_min hε1 (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) one_pos))))
  refine ⟨ε, 1 + π * C * √π, hεp, by positivity, ?_⟩
  intro h Y M hF hh hhε k hk1 hk2 hch
  obtain ⟨hε1', hεr⟩ := le_min_iff.1 hhε
  obtain ⟨hεδ0, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεδA, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεξ, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεξ3, hε1h⟩ := le_min_iff.1 hεr
  obtain ⟨δ, hδ, hδ3, J, m, N, κ, μ, hW⟩ := Hwin h Y M hF hh hεδA
  have hδ1 : δ ≤ 1 := by
    by_contra hcon; push Not at hcon
    have : 1 < δ ^ 3 := one_lt_pow₀ hcon (by norm_num : (3 : ℕ) ≠ 0)
    linarith only [this, hδ3, hε1h]
  have hδξ : δ ≤ ξ0 / 14 := bk_le_of_cube hδ (by positivity) (by rw [hδ3]; exact hεξ)
  have hδξ3 : δ ≤ ξ0 ^ 3 / (48 * (Cmu * cs + 1)) := bk_le_of_cube hδ (by positivity) (by rw [hδ3]; exact hεξ3)
  have hsharp := HS h Y M hF hh hε1' δ J m N κ μ hδ hδ3 hW
  have hbulk := HB h Y M hF hh hεδ0 δ J m N κ μ hδ hδ3 hW
  have hμ : |μ| ≤ δ ^ 3 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hμ, -⟩ := hW
    exact rk_mu_le hδ hδ1 hξ0 hCmu.le hcs0 hδξ (by simpa using hδξ3) hμ
  have hδ3le : δ ^ 3 ≤ 1 := by rw [hδ3]; exact hε1h
  -- `|κ| ≥ 1`
  have hκ1 : 1 ≤ |κ| := by
    have h1 : 1 ≤ κ ^ 2 * δ := by have := (abs_le.1 hsharp).1; linarith only [this]
    have h2 : κ ^ 2 * δ ≤ κ ^ 2 * 1 := mul_le_mul_of_nonneg_left hδ1 (sq_nonneg κ)
    by_contra hcon; push Not at hcon
    have h3 : |κ| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg κ) hcon (by norm_num)
    rw [sq_abs] at h3
    linarith only [h1, h2, h3]
  have hκpos : 0 < |κ| := by linarith only [hκ1]
  have hμκ : |μ| ≤ |κ| := by linarith only [hμ, hδ3le, hκ1]
  obtain ⟨s, hs1, hκs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ κ = s * |κ| := by
    rcases le_total 0 κ with h0 | h0
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h0]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_nonpos h0]; ring⟩
  -- the two sites
  set q0 : ℝ := ((k : ℝ) + θ) * h with hq0def
  set q1 : ℝ := ((k : ℝ) + 1 + θ) * h with hq1def
  have hh0 : 0 < h := hh
  have hqd0 : dlgQ (q₀ δ) (δ ^ 3) k = q0 := by rw [hq₀, hq0def, hδ3]
  have hqd1 : dlgQ (q₀ δ) (δ ^ 3) (k + 1) = q1 := by rw [hq₀, hq1def, hδ3]; push_cast; ring
  have hq01 : q0 ≤ q1 := by rw [hq0def, hq1def]; nlinarith only [hh0]
  have hqc0 : c ≤ dlgQ (q₀ δ) (δ ^ 3) k := by rw [hqd0]; linarith
  have hqb0 : dlgQ (q₀ δ) (δ ^ 3) k ≤ qs - η := by rw [hqd0]; linarith
  have hqc1 : c ≤ dlgQ (q₀ δ) (δ ^ 3) (k + 1) := by rw [hqd1]; linarith
  have hqb1 : dlgQ (q₀ δ) (δ ^ 3) (k + 1) ≤ qs - η := by rw [hqd1]; linarith
  have hq00 : 0 < q0 := by linarith
  have hq10 : 0 < q1 := by linarith
  have hq0q : q0 < qs := by linarith
  have hq1q : q1 < qs := by linarith
  have hb0 := hbulk k hqc0 hqb0
  have hb1 := hbulk (k + 1) hqc1 hqb1
  rw [hqd0] at hb0
  rw [hqd1] at hb1
  set ρ : ℝ := (δ ^ 3) ^ (1 / 6 : ℝ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hWpos : ∀ q : ℝ, 0 < q → q < qs → 0 < dlgsW (hrA1 P Q) (hrU P Q τ x) q := by
    intro q hq hqq
    rw [bkw_eq hP hQ hτ hs hspos hq hqq hα hβ]
    have hD : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (bk_sq_pos hq hqq)
    positivity
  have hχ0 := bk_chi_eq (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (c1 := (c / 2 + c) / 2) (q0 := q₀ δ) (δ := δ) (k := k)
    hP hQ hα hβ (by positivity) (by linarith) hq0q.le hqd0
  have hχ1 := bk_chi_eq (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) (c1 := (c / 2 + c) / 2) (q0 := q₀ δ) (δ := δ) (k := k + 1)
    hP hQ hα hβ (by positivity) (by linarith) hq1q.le hqd1
  rw [hχ0] at hb0
  rw [hχ1] at hb1
  have hanti := bk_phase_anti (P := P) (Q := Q) (τ := τ) (x := x) (qs := qs) hP hQ hα hβ hq00.le hq01 hq1q.le
  have hdiv : bkPhase P Q τ x qs q1 / δ ^ 3 ≤ bkPhase P Q τ x qs q0 / δ ^ 3 :=
    div_le_div_of_nonneg_right hanti (by positivity)
  obtain ⟨j, hj1, hj2⟩ := bk_zero_alg (ρ := ρ) (δ := δ) hρ0 (hWpos q0 hq00 hq0q) (hWpos q1 hq10 hq1q) hC.le hδ hκpos hμκ
    (by linarith) s hs1 hκs hch hb0 hb1
  rw [hδ3] at hj1 hj2
  have hE : |μ| / |κ| + π / 2 * (2 * C * √π * h) ≤ (1 + π * C * √π) * h := by
    have h1 : |μ| / |κ| ≤ h := by
      rw [div_le_iff₀ hκpos]
      have : |μ| ≤ h := by rw [← hδ3]; exact hμ
      nlinarith only [this, hκ1, abs_nonneg μ, hh]
    have h2 : π / 2 * (2 * C * √π * h) = π * C * √π * h := by ring
    rw [h2]; nlinarith only [h1]
  refine ⟨-j, ?_, ?_⟩
  · push_cast
    have : π * (-(j : ℝ) - 1 / 4) = π / 4 - (2 * j + 1) * π / 2 := by ring
    rw [this]
    have h3 : π / 4 - bkPhase P Q τ x qs q1 / h + (|μ| / |κ| + π / 2 * (2 * C * √π * h)) ≥ (2 * j + 1) * π / 2 := hj2
    linarith only [h3, hE]
  · push_cast
    have : π * (-(j : ℝ) - 1 / 4) = π / 4 - (2 * j + 1) * π / 2 := by ring
    rw [this]
    have h3 : π / 4 - bkPhase P Q τ x qs q0 / h - (|μ| / |κ| + π / 2 * (2 * C * √π * h)) ≤ (2 * j + 1) * π / 2 := hj1
    linarith only [h3, hE]

/-- info: 'FormalResearch.Special.bk_zeros_of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_zeros_of_out

end FormalResearch.Special
