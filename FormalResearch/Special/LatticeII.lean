module

public import FormalResearch.Special.LatticeSumII

/-!
# `lem:latticesum` (ii), abstract form

`‖∑_{x∈S} φ(x) - ∫_{-X}^{X} φ(s) t₀'(s) ds‖ ≤ (1+2ε) C_φ e^{-κX} + 2ε C_φ'/κ + B_{(i)}(φ')`,
with `φ' = deriv φ`, `C_φ' = C_φ e^{κr₀}/r₀` (Cauchy), `B_{(i)}` the bound of `latticeI_bound` for `φ'`
on the strip `|Im s| ≤ y₀ - r₀`.  See `LatticeSumII` for the structure of the argument.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma LevelData.mono_strip {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (h : LevelData τ0 X y0 m M K ε t S) {y1 : ℝ} (hy1 : 0 < y1) (hle : y1 ≤ y0) :
    LevelData τ0 X y1 m M K ε t S where
  cal := h.cal.mono hy1 hle
  eps := h.eps
  cont := h.cont
  mono := h.mono
  close := h.close
  mem := h.mem

end FormalResearch.Special.Lattice

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- The exact identity behind (ii): the sum minus the smooth integral, with explicit boundary
coefficients and the two correction integrals. -/
theorem sum_minus_integral_identity {X : ℝ} (hX : 0 < X) {S : Finset ℝ} {t t0 t0' : ℝ → ℝ}
    (hcount : ∀ s ∈ Icc (-X) X,
      (((S.filter (fun x => x ≤ s)).card : ℕ) : ℤ) = ⌊t s⌋ - ⌈t (-X)⌉ + 1)
    (hS : ∀ x ∈ S, x ∈ Icc (-X) X) {Φ Φ' : ℝ → ℂ} (hΦc : Continuous Φ)
    (hΦd : ∀ s ∈ Icc (-X) X, HasDerivAt Φ (Φ' s) s) (hΦ'c : ContinuousOn Φ' (Icc (-X) X))
    (ht0 : ∀ s ∈ Icc (-X) X, HasDerivAt t0 (t0' s) s) (ht0'c : ContinuousOn t0' (Icc (-X) X))
    (htc : Continuous t)
    (hfr : IntervalIntegrable (fun s => Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ)) volume (-X) X) :
    ∑ x ∈ S, Φ x - ∫ s in (-X)..X, Φ s * (t0' s : ℂ) =
      Φ X * ((⌊t X⌋ - t0 X + 1 / 2 : ℝ) : ℂ) + Φ (-X) * ((1 / 2 - ⌈t (-X)⌉ + t0 (-X) : ℝ) : ℂ)
      - (∫ s in (-X)..X, Φ' s * ((t s - t0 s : ℝ) : ℂ)) +
      ∫ s in (-X)..X, Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ) := by
  have hle : -X ≤ X := by linarith
  have hsbp := sum_by_parts hS hΦc hΦd hΦ'c hX.le
  have ht0c : ContinuousOn t0 (Icc (-X) X) := fun s hs => (ht0 s hs).continuousAt.continuousWithinAt
  have iΦ' : IntervalIntegrable Φ' volume (-X) X := hΦ'c.intervalIntegrable_of_Icc hle
  have iΦt0' : IntervalIntegrable (fun s => Φ s * (t0' s : ℂ)) volume (-X) X :=
    (hΦc.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn ht0'c)).intervalIntegrable_of_Icc hle
  have iA1 : IntervalIntegrable (fun s => Φ' s * (t0 s : ℂ)) volume (-X) X :=
    (hΦ'c.mul (Complex.continuous_ofReal.comp_continuousOn ht0c)).intervalIntegrable_of_Icc hle
  have iA2 : IntervalIntegrable (fun s => Φ' s * ((t s - t0 s : ℝ) : ℂ)) volume (-X) X :=
    (hΦ'c.mul (Complex.continuous_ofReal.comp_continuousOn
      (htc.continuousOn.sub ht0c))).intervalIntegrable_of_Icc hle
  -- IBP for A1
  have hibp : ∫ s in (-X)..X, (t0 s : ℂ) * Φ' s =
      (t0 X : ℂ) * Φ X - (t0 (-X) : ℂ) * Φ (-X) - ∫ s in (-X)..X, (t0' s : ℂ) * Φ s := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun s => (t0 s : ℂ))
      (u' := fun s => (t0' s : ℂ)) (v := Φ) (v' := Φ') ?_ ?_ ?_ iΦ'
    · intro s hs; rw [uIcc_of_le hle] at hs; exact (ht0 s hs).ofReal_comp
    · intro s hs; rw [uIcc_of_le hle] at hs; exact hΦd s hs
    · exact (Complex.continuous_ofReal.comp_continuousOn ht0'c).intervalIntegrable_of_Icc hle
  -- the counting function decomposes
  set c : ℤ := ⌈t (-X)⌉ with hc
  have hdec : ∀ s ∈ uIcc (-X) X, Φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) =
      Φ' s * (t0 s : ℂ) + Φ' s * ((t s - t0 s : ℝ) : ℂ) -
        Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ) + ((1 / 2 - c : ℝ) : ℂ) * Φ' s := by
    intro s hs
    rw [uIcc_of_le hle] at hs
    have h1 := hcount s hs
    have h2 : (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) = ((⌊t s⌋ - c + 1 : ℤ) : ℂ) := by
      rw [← h1]; norm_cast
    rw [h2]
    have h3 : (⌊t s⌋ : ℝ) = t s - Int.fract (t s) := by
      rw [Int.fract]; ring
    have h4 : ((⌊t s⌋ : ℤ) : ℂ) = ((t s - Int.fract (t s) : ℝ) : ℂ) := by
      rw [← h3]; norm_cast
    push_cast at h4 ⊢
    rw [h4]
    ring
  have hN : ∫ s in (-X)..X, Φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) =
      (∫ s in (-X)..X, Φ' s * (t0 s : ℂ)) + (∫ s in (-X)..X, Φ' s * ((t s - t0 s : ℝ) : ℂ)) -
        (∫ s in (-X)..X, Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ)) +
        ((1 / 2 - c : ℝ) : ℂ) * (Φ X - Φ (-X)) := by
    rw [intervalIntegral.integral_congr hdec]
    rw [intervalIntegral.integral_add ((iA1.add iA2).sub hfr) (iΦ'.const_mul _),
      intervalIntegral.integral_sub (iA1.add iA2) hfr, intervalIntegral.integral_add iA1 iA2,
      intervalIntegral.integral_const_mul]
    have hF : ∫ s in (-X)..X, Φ' s = Φ X - Φ (-X) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
        rw [uIcc_of_le hle] at hs; exact hΦd s hs) iΦ'
    rw [hF]
  have hA1 : ∫ s in (-X)..X, Φ' s * (t0 s : ℂ) =
      (t0 X : ℂ) * Φ X - (t0 (-X) : ℂ) * Φ (-X) - ∫ s in (-X)..X, Φ s * (t0' s : ℂ) := by
    have e1 : (fun s => Φ' s * (t0 s : ℂ)) = fun s => (t0 s : ℂ) * Φ' s := by ext s; ring
    have e2 : (fun s => Φ s * (t0' s : ℂ)) = fun s => (t0' s : ℂ) * Φ s := by ext s; ring
    rw [e1, e2]; exact hibp
  have hcardX : ((S.card : ℕ) : ℂ) = ((⌊t X⌋ - c + 1 : ℤ) : ℂ) := by
    have h1 := hcount X ⟨hle, le_rfl⟩
    have : S.filter (fun x => x ≤ X) = S := by
      ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro hx; exact (hS x hx).2
    rw [this] at h1
    rw [← h1]; norm_cast
  rw [hsbp, hN, hA1, hcardX]
  push_cast
  ring

end FormalResearch.Special.Lattice
