module

public import FormalResearch.Special.RacahKappaOsc
public import FormalResearch.Special.DiscreteLgBulk

/-!
# The mass of a Liouville-Green oscillation on a band (Airy-free, chain-free)

Let `(A, θ, w, Θ)` be a bulk LG datum (`DlgData`: `A w² sin θ = 1`, `Θ' = θ`, jets bounded by `M`, `lo ≤ A, w ≤ hi`) on an open convex set `U`, `q_i = q₀ + (a + i)h`,
and suppose a sequence `Y` has the LG form `Y_{a+i} = ρ w(q_i) (κ cos(Θ(q_i)/h + φ₀) + μ sin(Θ(q_i)/h + φ₀)) + O(E ρ (|κ|+|μ|) h w(q_i))` at the sites `i < N'`
(the conclusion of `dlg_bulk`/`dlg_hahn_airy`).  Then, with `R² = κ² + μ²`,

`|Σ_{i<N'} Y_{a+i}² - (ρ² R²/2) Σ_{i<N'} w(q_i)²| ≤ ρ² R² (4E(1+E) h Σ w(q_i)² + ½(hi⁵ + 2N'hM(hi⁴ + hi⁸)))`  (`rkb_band`).

The oscillating part `Σ w² cos(2Θ/h + …)` is `O(1)` by `rko_abel` (the increments of the phase are `2θ(ξ)`, `sin θ(ξ) = 1/(A w²) ≥ 1/hi³`, and they vary by `≤ 4Mh`); the error part is `O(h)` times
the main term.  So the band mass is `(ρ²R²/2) Σ w²` up to a relative `O(h)`: this is the mass accounting of the Hahn proof (`hahn3j_band_clean`) with the Ermakov invariant replaced
by the exact LG amplitude `ρ R w`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Polar form with `R² = α² + β²`. -/
lemma rkb_polar (α β : ℝ) : ∃ R φ : ℝ, 0 ≤ R ∧ R ^ 2 = α ^ 2 + β ^ 2 ∧
    ∀ P : ℝ, α * Real.cos P + β * Real.sin P = R * Real.cos (P - φ) := by
  refine ⟨‖(⟨α, β⟩ : ℂ)‖, Complex.arg ⟨α, β⟩, norm_nonneg _, ?_, fun P => ?_⟩
  · rw [Complex.sq_norm, Complex.normSq_mk]; ring
  · have h1 := Complex.norm_mul_cos_arg (⟨α, β⟩ : ℂ)
    have h2 := Complex.norm_mul_sin_arg (⟨α, β⟩ : ℂ)
    simp only at h1 h2
    rw [Real.cos_sub]
    linear_combination (-Real.cos P) * h1 + (-Real.sin P) * h2

/-- Mean value theorem for the LG phase on one lattice step. -/
lemma rkb_mvt {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M) {q h : ℝ} (hh : 0 < h)
    (hq : q ∈ U) (hqh : q + h ∈ U) : ∃ ξ ∈ Ioo q (q + h), ξ ∈ U ∧ Θ (q + h) - Θ q = h * θ ξ := by
  have hsub : Icc q (q + h) ⊆ U := D.convex.ordConnected.out hq hqh
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Θ θ (by linarith : q < q + h)
    (fun t ht => (D.Θd t (hsub ht)).continuousAt.continuousWithinAt)
    (fun t ht => D.Θd t (hsub (Ioo_subset_Icc_self ht)))
  refine ⟨c, hc, hsub (Ioo_subset_Icc_self hc), ?_⟩
  rw [add_sub_cancel_left] at hcd
  field_simp at hcd
  linarith

/-- `sin θ ≥ hi⁻³` on `U`. -/
lemma rkb_sin_ge {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M) {t : ℝ} (ht : t ∈ U) :
    1 / hi ^ 3 ≤ Real.sin (θ t) := by
  have h1 := D.rel t ht
  have hA := D.Ab t ht
  have hw := D.wb t ht
  have hlo := D.lo_pos
  have hAw : A t * w t ^ 2 ≤ hi ^ 3 := by
    have : w t ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (by linarith [hw.1]) hw.2 2
    calc A t * w t ^ 2 ≤ hi * hi ^ 2 := mul_le_mul hA.2 this (by positivity) (by linarith [hA.1])
      _ = hi ^ 3 := by ring
  have hApos : 0 < A t * w t ^ 2 := by
    have : 0 < A t := by linarith [hA.1]
    have : 0 < w t := by linarith [hw.1]
    positivity
  have hsin : Real.sin (θ t) = 1 / (A t * w t ^ 2) := by
    rw [eq_div_iff hApos.ne', mul_comm]; exact h1
  rw [hsin]
  exact one_div_le_one_div_of_le hApos hAw

/-- The oscillating part of the band mass: `|Σ w² cos(2(Θ/h + φ))| ≤ hi⁵ + 2N'hM(hi⁴ + hi⁸)`. -/
lemma rkb_osc {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M) {q0 h φ : ℝ} {a : ℤ}
    (N' : ℕ) (hh : 0 < h) (hq : ∀ i : ℕ, i ≤ N' → dlgQ q0 h (a + (i : ℤ)) ∈ U) :
    |∑ i ∈ range N', w (dlgQ q0 h (a + (i : ℤ))) ^ 2 * Real.cos (2 * (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ))| ≤
      hi ^ 5 + 2 * N' * h * M * (hi ^ 4 + hi ^ 8) := by
  have hlo := D.lo_pos
  have hwb : ∀ t ∈ U, 0 < w t ∧ w t ≤ hi := fun t ht => ⟨by linarith [(D.wb t ht).1], (D.wb t ht).2⟩
  have hhi : 0 < hi := by
    obtain ⟨t, ht⟩ : ∃ t, t ∈ U := ⟨_, hq 0 (Nat.zero_le _)⟩
    linarith [(D.wb t ht).1, (D.wb t ht).2]
  have hM := D.M_nonneg
  set Q : ℕ → ℝ := fun i => dlgQ q0 h (a + (i : ℤ)) with hQ
  have hQs : ∀ i : ℕ, Q (i + 1) = Q i + h := fun i => by
    simp only [hQ]; rw [show a + ((i + 1 : ℕ) : ℤ) = (a + (i : ℤ)) + 1 by push_cast; ring, dlgQ_succ]
  have hstep : ∀ i : ℕ, i + 1 ≤ N' → ∃ ξ ∈ Ioo (Q i) (Q i + h), ξ ∈ U ∧
      2 * (Θ (Q (i + 1)) / h + φ) - 2 * (Θ (Q i) / h + φ) = 2 * θ ξ := by
    intro i hi'
    obtain ⟨ξ, hξ, hξU, hξe⟩ := rkb_mvt D hh (hq i (by omega)) (by rw [← hQs]; exact hq (i + 1) hi')
    refine ⟨ξ, hξ, hξU, ?_⟩
    have : Θ (Q i + h) = Θ (Q i) + h * θ ξ := by linarith
    rw [hQs, this]; field_simp; ring
  set ε : ℝ := 2 / hi ^ 3 with hε
  have hεp : 0 < ε := by positivity
  have hLipθ : ∀ x ∈ U, ∀ y ∈ U, |θ y - θ x| ≤ M * |y - x| := fun x hx y hy =>
    dlg_lip D.convex (fun t ht => (dlg_hasDeriv2 D.isOpen D.θ2).1 t ht) (fun t ht => (D.jb t ht).2.2.1) hx hy
  have hLipw : ∀ x ∈ U, ∀ y ∈ U, |w y - w x| ≤ M * |y - x| := fun x hx y hy =>
    dlg_lip D.convex (fun t ht => (dlg_hasDeriv2 D.isOpen D.w2).1 t ht) (fun t ht => (D.jb t ht).2.2.2.2.1) hx hy
  have key := rko_abel (fun i => w (Q i) ^ 2) (fun i => 2 * (Θ (Q i) / h + φ)) N' (F := hi ^ 2) (F' := 2 * hi * M * h)
    (D := 4 * M * h) (ε := ε) hεp (by positivity) (by positivity) (by positivity)
    (fun i hi' => by
      have := hwb (Q i) (hq i hi'.le)
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ this.1.le this.2 2)
    (fun i hi' => by
      have hqi := hq i (by omega)
      have hqi1 : Q (i + 1) ∈ U := hq (i + 1) hi'.le
      have h1 := hLipw _ hqi _ hqi1
      rw [hQs] at h1 hqi1
      have e : |Q i + h - Q i| = h := by rw [add_sub_cancel_left, abs_of_pos hh]
      rw [e] at h1
      have h2 := hwb _ hqi
      have h3 := hwb _ hqi1
      show |w (Q (i + 1)) ^ 2 - w (Q i) ^ 2| ≤ _
      rw [hQs]
      have : w (Q i + h) ^ 2 - w (Q i) ^ 2 = (w (Q i + h) - w (Q i)) * (w (Q i + h) + w (Q i)) := by ring
      rw [this, abs_mul]
      have h4 : |w (Q i + h) + w (Q i)| ≤ 2 * hi := by
        rw [abs_of_pos (by linarith [h2.1, h3.1])]; linarith [h2.2, h3.2]
      calc |w (Q i + h) - w (Q i)| * |w (Q i + h) + w (Q i)| ≤ (M * h) * (2 * hi) :=
            mul_le_mul h1 h4 (abs_nonneg _) (by positivity)
        _ = 2 * hi * M * h := by ring)
    (fun i hi' => by
      obtain ⟨ξ, hξ, hξU, hξe⟩ := hstep i hi'
      show ε ≤ 2 * |Real.sin ((2 * (Θ (Q (i + 1)) / h + φ) - 2 * (Θ (Q i) / h + φ)) / 2)|
      rw [hξe, mul_div_cancel_left₀ _ (two_ne_zero)]
      have h1 := rkb_sin_ge D hξU
      have h0 : 0 < 1 / hi ^ 3 := by positivity
      rw [abs_of_nonneg (by linarith)]
      have e2 : ε = 2 * (1 / hi ^ 3) := by rw [hε]; ring
      rw [e2]; linarith)
    (fun i hi' => by
      obtain ⟨ξ, hξ, hξU, hξe⟩ := hstep i hi'.le
      obtain ⟨ξ', hξ', hξU', hξe'⟩ := hstep (i + 1) hi'
      show |(2 * (Θ (Q (i + 1 + 1)) / h + φ) - 2 * (Θ (Q (i + 1)) / h + φ)) -
        (2 * (Θ (Q (i + 1)) / h + φ) - 2 * (Θ (Q i) / h + φ))| ≤ _
      rw [hξe, hξe']
      have hd := hLipθ _ hξU _ hξU'
      rw [hQs i] at hξ'
      have hdist : |ξ' - ξ| ≤ 2 * h := by
        rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2, hξ'.1, hξ'.2]
      calc |2 * θ ξ' - 2 * θ ξ| = 2 * |θ ξ' - θ ξ| := by rw [← mul_sub, abs_mul]; norm_num
        _ ≤ 2 * (M * |ξ' - ξ|) := by linarith
        _ ≤ 2 * (M * (2 * h)) := by have := mul_le_mul_of_nonneg_left hdist hM; linarith
        _ = 4 * M * h := by ring)
  have e1 : ∀ i : ℕ, Real.cos (2 * (Θ (Q i) / h + φ)) = Real.cos (2 * (Θ (Q i) / h + φ)) := fun _ => rfl
  refine key.trans ?_
  have hε' : 2 * hi ^ 2 / ε = hi ^ 5 := by rw [hε]; field_simp
  have h2 : 2 * (N' : ℝ) * (2 * hi * M * h / ε + hi ^ 2 * (4 * M * h) / ε ^ 2) = 2 * N' * h * M * (hi ^ 4 + hi ^ 8) := by
    rw [hε]; field_simp; ring
  rw [hε', h2]

/-- **Band mass of a Liouville-Green oscillation** (see the module docstring). -/
theorem rkb_band {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M)
    {q0 h ρ E κ μ φ0 : ℝ} {a : ℤ} {Y : ℤ → ℝ} (N' : ℕ) (hh : 0 < h) (hh1 : h ≤ 1) (hρ : 0 ≤ ρ) (hE : 0 ≤ E)
    (hq : ∀ i : ℕ, i ≤ N' → dlgQ q0 h (a + (i : ℤ)) ∈ U)
    (hrep : ∀ i : ℕ, i < N' → |Y (a + (i : ℤ)) - ρ * w (dlgQ q0 h (a + (i : ℤ))) *
        (κ * Real.cos (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ0) + μ * Real.sin (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ0))| ≤
      E * ((|κ| + |μ|) * (ρ * h)) * w (dlgQ q0 h (a + (i : ℤ)))) :
    |∑ i ∈ range N', Y (a + (i : ℤ)) ^ 2 - ρ ^ 2 * (κ ^ 2 + μ ^ 2) / 2 * ∑ i ∈ range N', w (dlgQ q0 h (a + (i : ℤ))) ^ 2| ≤
      ρ ^ 2 * (κ ^ 2 + μ ^ 2) * (4 * E * (1 + E) * h * ∑ i ∈ range N', w (dlgQ q0 h (a + (i : ℤ))) ^ 2 +
        (hi ^ 5 + 2 * N' * h * M * (hi ^ 4 + hi ^ 8)) / 2) := by
  obtain ⟨R, φ, hR0, hR2, hpol⟩ := rkb_polar κ μ
  have hκR : |κ| ≤ R := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg μ]) hR0
  have hμR : |μ| ≤ R := abs_le_of_sq_le_sq (by nlinarith [sq_nonneg κ]) hR0
  have hlo := D.lo_pos
  have hwb : ∀ t ∈ U, 0 < w t := fun t ht => by linarith [(D.wb t ht).1]
  set Q : ℕ → ℝ := fun i => dlgQ q0 h (a + (i : ℤ)) with hQ
  set m : ℕ → ℝ := fun i => ρ * w (Q i) * R * Real.cos (Θ (Q i) / h + φ0 - φ) with hm
  have hpt : ∀ i ∈ range N', |Y (a + (i : ℤ)) ^ 2 - m i ^ 2| ≤ 4 * E * (1 + E) * h * (ρ ^ 2 * R ^ 2 * w (Q i) ^ 2) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hw0 := hwb (Q i) (hq i hi'.le)
    have h1 := hrep i hi'
    have hP := hpol (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ0)
    have h2 : |Y (a + (i : ℤ)) - m i| ≤ E * (2 * R) * (ρ * h) * w (Q i) := by
      have e : ρ * w (dlgQ q0 h (a + (i : ℤ))) * (κ * Real.cos (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ0) +
          μ * Real.sin (Θ (dlgQ q0 h (a + (i : ℤ))) / h + φ0)) = m i := by
        rw [hP]; simp only [hm, hQ]; ring_nf
      rw [e] at h1
      refine h1.trans ?_
      have : E * ((|κ| + |μ|) * (ρ * h)) ≤ E * (2 * R) * (ρ * h) := by
        have : (|κ| + |μ|) * (ρ * h) ≤ (2 * R) * (ρ * h) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        have := mul_le_mul_of_nonneg_left this hE
        linarith
      exact mul_le_mul_of_nonneg_right this hw0.le
    have h3 : |m i| ≤ ρ * w (Q i) * R := by
      simp only [hm]
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ρ * w (Q i) * R)]
      calc ρ * w (Q i) * R * |Real.cos (Θ (Q i) / h + φ0 - φ)| ≤ ρ * w (Q i) * R * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
        _ = ρ * w (Q i) * R := by ring
    have e : Y (a + (i : ℤ)) ^ 2 - m i ^ 2 = (Y (a + (i : ℤ)) - m i) * ((Y (a + (i : ℤ)) - m i) + 2 * m i) := by ring
    rw [e, abs_mul]
    have h4 : |(Y (a + (i : ℤ)) - m i) + 2 * m i| ≤ 2 * (ρ * w (Q i) * R) * (1 + E) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_two]
      have h5 : E * (2 * R) * (ρ * h) * w (Q i) ≤ E * (2 * (ρ * w (Q i) * R)) := by
        have h6 : 0 ≤ E * (2 * (ρ * w (Q i) * R)) := by positivity
        calc E * (2 * R) * (ρ * h) * w (Q i) = (E * (2 * (ρ * w (Q i) * R))) * h := by ring
          _ ≤ (E * (2 * (ρ * w (Q i) * R))) * 1 := mul_le_mul_of_nonneg_left hh1 h6
          _ = _ := by ring
      nlinarith [h2, h3, h5]
    calc |Y (a + (i : ℤ)) - m i| * |(Y (a + (i : ℤ)) - m i) + 2 * m i|
        ≤ (E * (2 * R) * (ρ * h) * w (Q i)) * (2 * (ρ * w (Q i) * R) * (1 + E)) :=
          mul_le_mul h2 h4 (abs_nonneg _) (by positivity)
      _ = 4 * E * (1 + E) * h * (ρ ^ 2 * R ^ 2 * w (Q i) ^ 2) := by ring
  have hsum1 : |∑ i ∈ range N', Y (a + (i : ℤ)) ^ 2 - ∑ i ∈ range N', m i ^ 2| ≤
      4 * E * (1 + E) * h * (ρ ^ 2 * R ^ 2 * ∑ i ∈ range N', w (Q i) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hcos : ∀ i ∈ range N', m i ^ 2 = ρ ^ 2 * R ^ 2 / 2 * (w (Q i) ^ 2 + w (Q i) ^ 2 * Real.cos (2 * (Θ (Q i) / h + (φ0 - φ)))) := by
    intro i _
    have : Real.cos (Θ (Q i) / h + φ0 - φ) ^ 2 = (1 + Real.cos (2 * (Θ (Q i) / h + (φ0 - φ)))) / 2 := by
      rw [Real.cos_sq]; ring_nf
    simp only [hm]
    calc (ρ * w (Q i) * R * Real.cos (Θ (Q i) / h + φ0 - φ)) ^ 2 = ρ ^ 2 * R ^ 2 * w (Q i) ^ 2 * Real.cos (Θ (Q i) / h + φ0 - φ) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have hsum2 : ∑ i ∈ range N', m i ^ 2 = ρ ^ 2 * R ^ 2 / 2 * (∑ i ∈ range N', w (Q i) ^ 2 +
      ∑ i ∈ range N', w (Q i) ^ 2 * Real.cos (2 * (Θ (Q i) / h + (φ0 - φ)))) := by
    rw [Finset.sum_congr rfl hcos, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hosc := rkb_osc D (q0 := q0) (h := h) (φ := φ0 - φ) (a := a) N' hh hq
  have hR2' : ρ ^ 2 * (κ ^ 2 + μ ^ 2) = ρ ^ 2 * R ^ 2 := by rw [hR2]
  rw [hR2']
  have hfin : ∑ i ∈ range N', Y (a + (i : ℤ)) ^ 2 - ρ ^ 2 * R ^ 2 / 2 * ∑ i ∈ range N', w (Q i) ^ 2 =
      (∑ i ∈ range N', Y (a + (i : ℤ)) ^ 2 - ∑ i ∈ range N', m i ^ 2) +
      ρ ^ 2 * R ^ 2 / 2 * ∑ i ∈ range N', w (Q i) ^ 2 * Real.cos (2 * (Θ (Q i) / h + (φ0 - φ))) := by
    rw [hsum2]; ring
  show |∑ i ∈ range N', Y (a + (i : ℤ)) ^ 2 - ρ ^ 2 * R ^ 2 / 2 * ∑ i ∈ range N', w (Q i) ^ 2| ≤ _
  rw [hfin]
  refine (abs_add_le _ _).trans ?_
  have hc : |ρ ^ 2 * R ^ 2 / 2 * ∑ i ∈ range N', w (Q i) ^ 2 * Real.cos (2 * (Θ (Q i) / h + (φ0 - φ)))| ≤
      ρ ^ 2 * R ^ 2 / 2 * (hi ^ 5 + 2 * N' * h * M * (hi ^ 4 + hi ^ 8)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ρ ^ 2 * R ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left hosc (by positivity)
  nlinarith [hsum1, hc]

/-- info: 'FormalResearch.Special.rkb_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rkb_band

end FormalResearch.Special
