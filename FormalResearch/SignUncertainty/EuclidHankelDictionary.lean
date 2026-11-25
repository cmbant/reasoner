module

public import FormalResearch.SignUncertainty.Radii
public import FormalResearch.SignUncertainty.EuclidRadialHankel

/-!
# The Euclidean-to-Hankel dictionary (`gt:7.9`, proof)

For every integer `d ≥ 2`, `A_sign^+(d)²/2 = T_{d/2}^{+1}` and `A_sign^-(d)²/2 = T_{d/2}^{-1,0}`
(`hankel_euclid_dictionary_of_radial_projection`).

* **Hankel to Euclid** (proved here, every integer `d ≥ 2`): a Hankel-feasible `G` at threshold `T`
  gives the sign-uncertainty competitor `x ↦ G(‖x‖²/2)` of radius `√(2 max(T,0))`
  (`signWitness_of_hankelFeasible`), by `fourier_radial_hankel` and `integrable_radialLift_iff`.
* **Positivity** (proved): every competitor has radius `R > 0` (`IsSignWitness.pos_radius`).
* **Euclid to Hankel** is the hypothesis `RadialProjection`: the `O(d)`-average of a competitor is a
  nonzero radial competitor with the same value at the origin and the same radius (average over the
  sphere, which commutes with `𝓕`, and the compact-support uncertainty argument that the average is
  nonzero).
* The infima are matched by `sInf_sq_div_two_eq`, which uses only the three properties above.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The Euclid-to-Hankel step of `gt:7.9` (radial averaging over `O(d)` plus the compact-support
uncertainty argument): a competitor `f` for the sign `ε = ±1` with `ε f(0) ≤ 0` and radius `R` yields a
Hankel-feasible `G` at `R²/2` with `G(0) = f(0)`. -/
def RadialProjection : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (R : ℝ) (f : Euc d → ℝ),
    IsSignWitness ε d R f → ε * f 0 ≤ 0 →
      ∃ G : ℝ → ℝ, IsHankelFeasible ((d : ℝ) / 2) ε (R ^ 2 / 2) G ∧ G 0 = f 0

/-- A function with a.e. vanishing values has vanishing Fourier transform. -/
lemma fourier_eq_zero_of_ae_zero {d : ℕ} {f : Euc d → ℝ} (h : f =ᵐ[volume] 0) (y : Euc d) :
    𝓕 (fun x : Euc d => (f x : ℂ)) y = 0 := by
  rw [Real.fourier_eq]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

/-- Every sign-uncertainty competitor has a positive radius (given `ε f(0) ≤ 0`): otherwise `f ≥ 0`
everywhere, `∫ f = 𝓕 f(0) = ε f(0) ≤ 0` forces `f = 0` a.e., so `𝓕 f = 0 = ε f`. -/
lemma IsSignWitness.pos_radius {ε : ℝ} {d : ℕ} {R : ℝ} {f : Euc d → ℝ}
    (h : IsSignWitness ε d R f) (hε : ε = 1 ∨ ε = -1) (h0 : ε * f 0 ≤ 0) : 0 < R := by
  by_contra hR
  push Not at hR
  have hnn : ∀ x, 0 ≤ f x := fun x => h.tail_nonneg x (hR.trans (norm_nonneg x))
  have hF0 := h.fourier_eq 0
  have hint : 𝓕 (fun x : Euc d => (f x : ℂ)) 0 = ((∫ x, f x : ℝ) : ℂ) := by
    rw [Real.fourier_eq]
    simp [integral_complex_ofReal]
  rw [hint, ← Complex.ofReal_mul, Complex.ofReal_inj] at hF0
  have hI0 : 0 ≤ ∫ x, f x := integral_nonneg hnn
  have hz : ∫ x, f x = 0 := le_antisymm (hF0 ▸ h0) hI0
  have hae : f =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn h.integrable).1 hz
  obtain ⟨x, hx⟩ := h.nonzero
  have := h.fourier_eq x
  rw [fourier_eq_zero_of_ae_zero hae x] at this
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have : (ε : ℂ) * (f x : ℂ) = 0 := this.symm
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hε0 (by exact_mod_cast h1)
  · exact hx (by exact_mod_cast h1)

/-- **Hankel to Euclid.** A Hankel-feasible `G` at `T` (dimension `d = n + 1 ≥ 2`) gives the
competitor `x ↦ G(‖x‖²/2)` of radius `√(2 max(T,0))`. -/
theorem signWitness_of_hankelFeasible (n : ℕ) (hn : 1 ≤ n) {ε T : ℝ} {G : ℝ → ℝ}
    (hf : IsHankelFeasible (((n + 1 : ℕ) : ℝ) / 2) ε T G) :
    IsSignWitness ε (n + 1) (√(2 * max T 0)) (fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2)) := by
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  rw [hc] at hf
  have hint : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) :=
    (integrable_radialLift_iff n hn G).2 hf.int
  refine ⟨?_, fun y => ?_, ?_, fun x hx => ?_⟩
  · simpa using hint.re
  · have := fourier_radial_hankel n hn hf.cont hint y
    rw [this, hf.eigen _ (mem_Ici.2 (by positivity))]
    push_cast; rfl
  · obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
    refine ⟨EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ), ?_⟩
    simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (by have := mem_Ici.1 hΔ; positivity)]
    simpa using hne
  · refine hf.tail_nonneg _ ?_
    have h1 : √(2 * max T 0) ^ 2 ≤ ‖x‖ ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    rw [Real.sq_sqrt (by positivity)] at h1
    have := le_max_left T 0
    linarith

/-- **Matching infima.** If `A, B ⊆ ℝ` satisfy: every `R ∈ A` is positive and `R²/2 ∈ B`, and every
`T ∈ B` is positive with `√(2T) ∈ A`, then `(sInf A)²/2 = sInf B` (including the empty case). -/
lemma sInf_sq_div_two_eq {A B : Set ℝ} (hA : ∀ R ∈ A, 0 < R) (hAB : ∀ R ∈ A, R ^ 2 / 2 ∈ B)
    (hBA : ∀ T ∈ B, 0 < T ∧ √(2 * T) ∈ A) : (sInf A) ^ 2 / 2 = sInf B := by
  let g : ℝ → ℝ := fun x => (max x 0) ^ 2 / 2
  have hg_mono : Monotone g := fun x y hxy => by
    have h0 : 0 ≤ max x 0 := le_max_right _ _
    have : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
    simp only [g]; nlinarith
  have hg_cont : Continuous g := by fun_prop
  have hB : B = g '' A := by
    ext T
    constructor
    · intro hT
      obtain ⟨hT0, hTA⟩ := hBA T hT
      refine ⟨√(2 * T), hTA, ?_⟩
      simp only [g, max_eq_left (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt (by positivity)]; ring
    · rintro ⟨R, hR, rfl⟩
      simp only [g, max_eq_left (hA R hR).le]
      exact hAB R hR
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hBe : B = ∅ := by rw [hB, hAe]; simp
    rw [hAe, hBe]; simp
  · have hbdd : BddBelow A := ⟨0, fun R hR => (hA R hR).le⟩
    have h := hg_mono.map_csInf_of_continuousAt hg_cont.continuousAt hAne hbdd
    have ha0 : 0 ≤ sInf A := Real.sInf_nonneg fun R hR => (hA R hR).le
    rw [hB, ← h]
    simp only [g, max_eq_left ha0]

/-- **`gt:7.9` (Euclidean-to-Hankel dictionary), from `RadialProjection`.** For every integer `d ≥ 2`,
`A_sign^+(d)²/2 = T_{d/2}^{+1}` and `A_sign^-(d)²/2 = T_{d/2}^{-1,0}`. -/
theorem hankel_euclid_dictionary_of_radial_projection (RP : RadialProjection) (d : ℕ) (hd : 2 ≤ d) :
    aSignPos d ^ 2 / 2 = hankelT 1 ((d : ℝ) / 2) ∧ aSignNeg d ^ 2 / 2 = hankelT0 ((d : ℝ) / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  refine ⟨sInf_sq_div_two_eq ?_ ?_ ?_, sInf_sq_div_two_eq ?_ ?_ ?_⟩
  · rintro R ⟨f, hf, h0⟩
    exact hf.pos_radius (Or.inl rfl) (by simpa using h0)
  · rintro R ⟨f, hf, h0⟩
    obtain ⟨G, hG, -⟩ := RP (n + 1) hd 1 (Or.inl rfl) R f hf (by simpa using h0)
    exact ⟨G, hG⟩
  · rintro T ⟨G, hG⟩
    have hW := signWitness_of_hankelFeasible n hn hG
    have hG0 : (fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2)) 0 ≤ 0 := by
      simpa using hG.origin_sign
    have hR : 0 < √(2 * max T 0) := hW.pos_radius (Or.inl rfl) (by simpa using hG0)
    have hT : 0 < T := by
      have := Real.sqrt_pos.1 hR
      by_contra hT'
      rw [max_eq_right (not_lt.1 hT')] at this
      linarith
    rw [max_eq_left hT.le] at hW
    exact ⟨hT, _, hW, hG0⟩
  · rintro R ⟨f, hf, h0⟩
    exact hf.pos_radius (Or.inr rfl) (by simp [h0])
  · rintro R ⟨f, hf, h0⟩
    obtain ⟨G, hG, hG0⟩ := RP (n + 1) hd (-1) (Or.inr rfl) R f hf (by simp [h0])
    exact ⟨G, hG, by rw [hG0, h0]⟩
  · rintro T ⟨G, hG, hG0⟩
    have hW := signWitness_of_hankelFeasible n hn hG
    have hG0' : (fun x : Euc (n + 1) => G (‖x‖ ^ 2 / 2)) 0 = 0 := by simpa using hG0
    have hR : 0 < √(2 * max T 0) := hW.pos_radius (Or.inr rfl) (by simp [hG0])
    have hT : 0 < T := by
      have := Real.sqrt_pos.1 hR
      by_contra hT'
      rw [max_eq_right (not_lt.1 hT')] at this
      linarith
    rw [max_eq_left hT.le] at hW
    exact ⟨hT, _, hW, hG0'⟩

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.hankel_euclid_dictionary_of_radial_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_euclid_dictionary_of_radial_projection

/-- info: 'FormalResearch.SignUncertainty.signWitness_of_hankelFeasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms signWitness_of_hankelFeasible

end FormalResearch.SignUncertainty
