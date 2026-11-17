module

public import FormalResearch.Special.BulkKappaAmp
public import FormalResearch.Special.BulkKappaSharp

/-!
# Explicit bulk theorem: amplitude `(2/√π)(s(q_*² - q²))^{-1/4}`, phase `Φ(q)/h - π/4`

`bk_explicit_of_out`: composition of the sharp amplitude `|κ² δ - 2| ≤ τ'` and the Liouville-Green bulk form of **the same Airy window** (`BkOut`, `bk_sharp_abs(H)`) with the closed forms of
`BulkKappaAmp`.  For a family `Fam` as in `bk_sharp_abs(H)` (the actual `3j` / `6j` chains at the lattice nodes), every compact bulk window `[a, b] ⊂ (0, q_*)` and every `t > 0` there is `ε` such that every member with `h ≤ ε`
has a sign `s ∈ {±1}` (the sign of `κ`) with

`|Y_k - s A(q_k) cos(Φ(q_k)/h - π/4)| ≤ t A(q_k)`   for every site `q_k = (k + θ) h ∈ [a, b]`,

`A(q) = (2/√π)(s_R (q_*² - q²))^{-1/4}` (`bkAmp`, `s_R = rkS P Q x`; `s_R = 1` for `3j`), `Φ(q) = ∫_q^{q_*} arccos u` (`bkPhase`).  In the form of the brief: `Y_k = A_* cos(Θ(q_k)/h - Θ_*/h + π/4 + ε_k)·w(q_k)`, amplitude and phase pinned,
the global sign `s` of `κ` left open.

**Claim class: proved.**  **Not formalised:** the sign `s` (it is the sign of the Airy coefficient `κ` of the window; the value `(-1)^{#nodes}` relative to a gauge needs the `O(1)` phase of the bulk
form, which is `π/4` here, plus a node count), a rate in `t`, uniformity of `ε` in `(a, b)` or in the data.
-/

@[expose] public section

open Finset Set FormalResearch.Racah.P3 FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

lemma bk_sq_pos {q qs : ℝ} (h0 : 0 < q) (h1 : q < qs) : 0 < qs ^ 2 - q ^ 2 := by nlinarith only [h0, h1]

/-- **Explicit bulk theorem, abstract form** (see the module docstring). -/
theorem bk_explicit_of_out {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2)
    {θ : ℝ} {q₀ : ℝ → ℝ} (hq₀ : ∀ δ : ℝ, ∀ k : ℤ, dlgQ (q₀ δ) (δ ^ 3) k = ((k : ℝ) + θ) * δ ^ 3)
    {Fam : ℝ → (ℤ → ℝ) → ℝ → Prop} {r Cmu ξ0 gmax gmin c1 c2 CA δA : ℝ} (hr : 0 < r) (hrq4 : r ≤ qs / 4) (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0)
    (Hout : BkOut θ q₀ P Q τ x qs Fam r Cmu ξ0 gmax gmin c1 c2 CA δA) (hδA : 0 < δA) :
    ∀ a b : ℝ, 0 < a → a < b → b < qs → ∀ t : ℝ, 0 < t → ∃ ε : ℝ, 0 < ε ∧ ∀ (h : ℝ) (Y : ℤ → ℝ) (M : ℝ), Fam h Y M → 0 < h → h ≤ ε →
      ∃ δ : ℝ, 0 < δ ∧ δ ^ 3 = h ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ k : ℤ, a ≤ ((k : ℝ) + θ) * h → ((k : ℝ) + θ) * h ≤ b →
        |Y k - s * bkAmp P Q x qs (((k : ℝ) + θ) * h) * Real.cos (bkPhase P Q τ x qs (((k : ℝ) + θ) * h) / h - π / 4)| ≤
          t * bkAmp P Q x qs (((k : ℝ) + θ) * h) := by
  obtain ⟨Hwin, Hsharp, Hbulk⟩ := Hout
  intro a b ha hab hbq t ht
  have hsq : 0 < Real.sqrt (rkS P Q x) := Real.sqrt_pos.2 hspos
  set cs : ℝ := 1 / Real.sqrt (rkS P Q x) + 1 with hcs
  have hcs0 : 0 ≤ cs := by positivity
  -- the bulk window `[c, qs - η]`
  set c : ℝ := min a (qs / 2) with hcdef
  have hc0 : 0 < c := lt_min ha (by positivity)
  have hca : c ≤ a := min_le_left _ _
  have hcq : c ≤ qs / 2 := min_le_right _ _
  set η : ℝ := min (qs - b) (r / 2) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηb : η ≤ qs - b := min_le_left _ _
  have hηr : η ≤ r / 2 := min_le_right _ _
  obtain ⟨δ0, C, hδ0, hC, HB⟩ := Hbulk (c / 2) (by positivity) (by linarith) η hη hηr c (by linarith) (by linarith)
  set t1 : ℝ := min 1 t with ht1def
  have ht1 : 0 < t1 := lt_min one_pos ht
  have ht11 : t1 ≤ 1 := min_le_left _ _
  have ht1t : t1 ≤ t := min_le_right _ _
  obtain ⟨ε1, hε1, HS⟩ := Hsharp t1 ht1
  set θ1 : ℝ := t / (2 * (1 + 6 * C)) with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set ε : ℝ := min ε1 (min (δ0 ^ 3) (min (δA ^ 3) (min ((ξ0 / 14) ^ 3) (min ((ξ0 ^ 3 / (48 * (Cmu * cs + 1))) ^ 3)
    (min 1 θ1))))) with hεdef
  have hεp : 0 < ε := lt_min hε1 (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (lt_min one_pos hθ1p)))))
  refine ⟨ε, hεp, ?_⟩
  intro h Y M hF hh hhε
  obtain ⟨hε1', hεr⟩ := le_min_iff.1 hhε
  obtain ⟨hεδ0, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεδA, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεξ, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hεξ3, hεr⟩ := le_min_iff.1 hεr
  obtain ⟨hε1h, hεθ⟩ := le_min_iff.1 hεr
  obtain ⟨δ, hδ, hδ3, J, m, N, κ, μ, hW⟩ := Hwin h Y M hF hh hεδA
  have hδ1 : δ ≤ 1 := by
    have : δ ^ 3 ≤ 1  := by rw [hδ3]; exact hε1h
    by_contra hcon; push Not at hcon
    have : 1 < δ ^ 3 := one_lt_pow₀ hcon (by norm_num : (3 : ℕ) ≠ 0)
    linarith only [this, ‹δ ^ 3 ≤ 1›]
  have hδξ : δ ≤ ξ0 / 14 := bk_le_of_cube hδ (by positivity) (by rw [hδ3]; exact hεξ)
  have hδξ3 : δ ≤ ξ0 ^ 3 / (48 * (Cmu * cs + 1)) := bk_le_of_cube hδ (by positivity) (by rw [hδ3]; exact hεξ3)
  have hδ0' : δ ≤ δ0 := bk_le_of_cube hδ hδ0 (by rw [hδ3]; exact hεδ0)
  have hsharp := HS h Y M hF hh hε1' δ J m N κ μ hδ hδ3 hW
  have hbulk := HB h Y M hF hh hεδ0 δ J m N κ μ hδ hδ3 hW
  -- `|μ| ≤ δ³`
  have hμ : |μ| ≤ δ ^ 3 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hμ, -⟩ := hW
    exact rk_mu_le hδ hδ1 hξ0 hCmu.le hcs0 hδξ (by simpa using hδξ3) hμ
  have hδθ : δ ^ 3 ≤ θ1 := by rw [hδ3]; exact hεθ
  obtain ⟨s, hs1, hκs⟩ : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ κ = s * |κ| := by
    rcases le_total 0 κ with h0 | h0
    · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h0]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_nonpos h0]; ring⟩
  refine ⟨δ, hδ, hδ3, s, hs1, ?_⟩
  intro k hk1 hk2
  -- the site
  set q : ℝ := ((k : ℝ) + θ) * h with hq
  have hqd : dlgQ (q₀ δ) (δ ^ 3) k = q := by rw [hq₀, hq, hδ3]
  have hqc : c ≤ dlgQ (q₀ δ) (δ ^ 3) k := by rw [hqd]; linarith
  have hqb : dlgQ (q₀ δ) (δ ^ 3) k ≤ qs - η := by rw [hqd]; linarith
  have hq0 : 0 < q := by linarith
  have hqq : q < qs := by linarith
  have hb := hbulk k hqc hqb
  rw [hqd] at hb
  set ρ : ℝ := (δ ^ 3) ^ (1 / 6 : ℝ) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by positivity) _
  have hρδ : ρ ^ 2 = δ := rk_rpow_sq hδ
  have hρ1 : ρ ≤ 1 := by
    by_contra hcon; push Not at hcon
    have h2 : 1 < ρ ^ 2 := by nlinarith only [hcon]
    linarith only [h2, hρδ, hδ1]
  have hWpos : 0 < dlgsW (hrA1 P Q) (hrU P Q τ x) q := by
    rw [bkw_eq hP hQ hτ hs hspos hq0 hqq hα hβ]
    have hD : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (bk_sq_pos hq0 hqq)
    positivity
  have hpha : ∀ χ0 : ℝ, χ0 = dlgP (dlgsPhase (hrU P Q τ x) ((c / 2 + c) / 2)) (q₀ δ) (δ ^ 3) k -
      (∫ s in (c / 2 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4 →
      Real.cos χ0 = Real.cos (bkPhase P Q τ x qs q / h - π / 4) := by
    intro χ0 hχ0
    have h1 : dlgP (dlgsPhase (hrU P Q τ x) ((c / 2 + c) / 2)) (q₀ δ) (δ ^ 3) k -
        (∫ s in (c / 2 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 = -(bkPhase P Q τ x qs q / h) := by
      unfold dlgP
      rw [hqd, ← sub_div, bk_phase_sub (bk_cont hP hQ hα hβ (by positivity)) (by linarith) hqq.le, hδ3]
      ring
    rw [hχ0, h1, ← Real.cos_neg]
    congr 1; ring
  have hest := bk_amp_est (Y := Y k) (ρ := ρ) (δ := δ) (W := dlgsW (hrA1 P Q) (hrU P Q τ x) q) (κ := κ) (μ := μ)
    (χ := dlgP (dlgsPhase (hrU P Q τ x) ((c / 2 + c) / 2)) (q₀ δ) (δ ^ 3) k -
      (∫ s in (c / 2 + c) / 2..qs, Real.arccos (hrU P Q τ x s)) / δ ^ 3 + π / 4) (C := C) (t := t1) (m := δ ^ 3)
    hρ0 hρδ hWpos hC.le ht11 (by positivity) hδ hsharp ((mul_le_of_le_one_left (abs_nonneg _) hρ1).trans hμ) s hs1 hκs hb
  rw [hpha _ rfl] at hest
  have hA : √2 * (1 / √π) * dlgsW (hrA1 P Q) (hrU P Q τ x) q = bkAmp P Q x qs q := by
    rw [bkw_eq hP hQ hτ hs hspos hq0 hqq hα hβ]
    unfold bkAmp
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc √2 * (1 / √π) * (√2 * (√√(rkS P Q x * (qs ^ 2 - q ^ 2)))⁻¹) =
        (√2 * √2) * (1 / √π) * (√√(rkS P Q x * (qs ^ 2 - q ^ 2)))⁻¹ := by ring
      _ = 2 / √π * (√√(rkS P Q x * (qs ^ 2 - q ^ 2)))⁻¹ := by rw [h2]; ring
  rw [hA] at hest
  refine hest.trans ?_
  have hApos : 0 ≤ bkAmp P Q x qs q := by
    unfold bkAmp
    have hD : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (bk_sq_pos hq0 hqq)
    positivity
  rw [mul_comm t]
  apply mul_le_mul_of_nonneg_left _ hApos
  have h3 : δ ^ 3 ≤ 1 := by rw [hδ3]; exact hε1h
  have h4 : 2 * C * (2 + δ ^ 3) * δ ^ 3 ≤ 6 * C * δ ^ 3 := by
    have : 2 + δ ^ 3 ≤ 3 := by linarith only [h3]
    nlinarith only [mul_nonneg hC.le (pow_nonneg hδ.le 3), this, hC]
  have h5 : (1 + 6 * C) * θ1 = t / 2 := by rw [hθ1]; field_simp
  have h6 : (1 + 6 * C) * δ ^ 3 ≤ (1 + 6 * C) * θ1 := mul_le_mul_of_nonneg_left hδθ (by positivity)
  nlinarith only [h4, h5, h6, ht1t, hC, hδ3, h3]

/-- info: 'FormalResearch.Special.bk_explicit_of_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bk_explicit_of_out

end FormalResearch.Special
