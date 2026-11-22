module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCExact
public import FormalResearch.Special.HermiteBulkMain

/-!
# Paper J, Layer 4 (phase B1): the oscillatory phase expansion of `U` on the lattice `mu^2 = 2n+1`

`pc_phase_osc_lattice` (`PCPhaseFact`, DLMF 12.10.18 on the lattice): for the actual `pcU`, `0 < eps < 1`, there are `C, mu0, g > 0` with
`|U(-mu^2/2, mu t sqrt 2) - 2 g(mu) (1-t^2)^{-1/4} cos(mu^2 eta(t) - pi/4)| <= C mu^{-2} 2 g(mu) (1-t^2)^{-1/4}` for `|t| <= 1 - eps`, `mu >= mu0`,
`mu^2 = 2n+1`, `eta = (arccos t - t sqrt(1-t^2))/2`.

Proof: `U(-n-1/2, z) = e^{-z^2/4} He_n(z)` (vendored DLMF 12.7.2, `parabolicCylinderD_nat`) is `pi^{1/4} sqrt(n!) phi_n(z/sqrt 2)` for the orthonormal Hermite
function `phi_n` (`Special.HermiteFunction`), and the Plancherel-Rotach theorem `Special.hermite_bulk_PR` (`|R| <= C/(n+1)`, `|x| <= (1-eps) sqrt(2n+1)`)
gives the expansion with `2 g(mu) = pi^{1/4} sqrt(n!) sqrt(2/pi) (2n+1)^{-1/4}` (extended by the same formula with `n = floor((mu^2-1)/2)` off the lattice, so that
`g > 0` everywhere), and error constant `2 C` since `1/(n+1) <= 2/(2n+1)`.

**Statement difference.**  `PCPhaseFact.phase_osc` is stated on the lattice only (`exists n, mu^2 = 2n+1`): the form for all real `mu >= mu0` has no proof in the vendored
lean-DLMF (its 12.10.18-21 are unproved) nor in this repository, and every consumer (`phase_pack`, `bulk_phase_left`) instantiates `mu^2 = 2n+1`.
-/

@[expose] public section
noncomputable section
namespace FormalResearch.JacobiEigenvectors.Charts
open DLMF.Confluent FormalResearch.Special

lemma pcU_nat (n : ℕ) (x : ℝ) :
    pcU (-(n : ℝ) - 1 / 2) x = Real.exp (-x ^ 2 / 4) * (heR n).eval x := by
  have h := parabolicCylinderD_nat n (x : ℂ)
  have e : parabolicCylinderD (n : ℂ) (x : ℂ) = ((pcU (-(n : ℝ) - 1 / 2) x : ℝ) : ℂ) := by
    rw [← pcU_ofReal]; unfold parabolicCylinderD; push_cast; rfl
  rw [e] at h
  have hp : Polynomial.aeval (x : ℂ) (Polynomial.hermite n) = (((heR n).eval x : ℝ) : ℂ) := by
    have := Polynomial.aeval_algebraMap_apply (A := ℝ) (B := ℂ) x (Polynomial.hermite n)
    rw [show (algebraMap ℝ ℂ) x = (x : ℂ) from rfl] at this
    rw [this]
    have hq : Polynomial.aeval x (Polynomial.hermite n) = (heR n).eval x := by
      rw [heR, Polynomial.eval_map, Polynomial.aeval_def]; rfl
    rw [hq]; rfl
  rw [hp] at h
  have h3 : Complex.exp (-(x : ℂ) ^ 2 / 4) = ((Real.exp (-x ^ 2 / 4) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [h3] at h
  exact_mod_cast h


/-- `U(-n-1/2, sqrt 2 x) = pi^{1/4} sqrt(n!) phi_n(x)`. -/
lemma pcU_eq_hermitePhi (n : ℕ) (x : ℝ) :
    pcU (-(n : ℝ) - 1 / 2) (Real.sqrt 2 * x) = Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ) * hermitePhi n x := by
  rw [pcU_nat, hermitePhi]
  have h2 : (Real.sqrt 2 * x) ^ 2 / 4 = x ^ 2 / 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; ring
  have hK : Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ) ≠ 0 := by positivity
  rw [show -(Real.sqrt 2 * x) ^ 2 / 4 = -((Real.sqrt 2 * x) ^ 2 / 4) by ring, h2]
  field_simp

theorem pc_phase_osc_lattice (eps : ℝ) (hε0 : 0 < eps) (hε1 : eps < 1) :
    ∃ C μ0 : ℝ, ∃ g : ℝ → ℝ, (∀ μ, 0 < g μ) ∧ ∀ μ : ℝ, μ0 ≤ μ → (∃ n : ℕ, μ ^ 2 = 2 * n + 1) →
      ∀ t : ℝ, |t| ≤ 1 - eps →
      |pcU (-(μ ^ 2) / 2) (μ * t * Real.sqrt 2) - 2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)
        * Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4)|
        ≤ C * μ⁻¹ ^ 2 * (2 * g μ / (1 - t ^ 2) ^ ((1 : ℝ) / 4)) := by
  obtain ⟨C, hC, hPR⟩ := hermite_bulk_PR eps hε0 hε1.le
  refine ⟨2 * C, 0, fun μ => (1 / 2) * (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt ((⌊(μ ^ 2 - 1) / 2⌋₊).factorial : ℝ))
      * (Real.sqrt (2 / Real.pi) * (2 * (⌊(μ ^ 2 - 1) / 2⌋₊ : ℝ) + 1) ^ (-(1 / 4 : ℝ))), ?_, ?_⟩
  · intro μ; positivity
  · rintro μ hμ0 ⟨n, hn⟩ t ht
    have hfl : ⌊(μ ^ 2 - 1) / 2⌋₊ = n := by
      rw [show (μ ^ 2 - 1) / 2 = (n : ℝ) by linarith]; exact Nat.floor_natCast n
    simp only [hfl]
    have hL : (0 : ℝ) < 2 * n + 1 := by positivity
    have hμpos : 0 < μ := by
      rcases hμ0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hn; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hsL : Real.sqrt (2 * (n : ℝ) + 1) = μ := by rw [← hn]; exact Real.sqrt_sq hμpos.le
    have ht1 : |t| ≤ 1 := by linarith
    have ht1' : |t| < 1 := by linarith
    have hx : |μ * t| ≤ (1 - eps) * Real.sqrt (2 * (n : ℝ) + 1) := by
      rw [hsL, abs_mul, abs_of_pos hμpos]; nlinarith
    obtain ⟨R, hR, hφ⟩ := hPR n (μ * t) hx
    have hz : μ * t * Real.sqrt 2 = Real.sqrt 2 * (μ * t) := by ring
    have ha : -(μ ^ 2) / 2 = -(n : ℝ) - 1 / 2 := by rw [hn]; ring
    rw [hz, ha, pcU_eq_hermitePhi, hφ]
    have hang : hpr_angle (μ * t) n = Real.arccos t := by
      unfold hpr_angle; rw [hsL]; congr 1; field_simp
    have ht1a : -1 ≤ t ∧ t ≤ 1 := abs_le.mp ht1
    have hsin : Real.sin (Real.arccos t) = Real.sqrt (1 - t ^ 2) := Real.sin_arccos t
    have hcos : Real.cos (Real.arccos t) = t := Real.cos_arccos ht1a.1 ht1a.2
    have hpos : 0 < 1 - t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have hph : hpr_phase (μ * t) n = μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4 := by
      unfold hpr_phase; rw [hang, Real.sin_two_mul, hsin, hcos, hn]; ring
    have hsr : Real.sqrt (1 - t ^ 2) ^ (-(1 / 2 : ℝ)) = ((1 - t ^ 2) ^ ((1 : ℝ) / 4))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one, ← Real.rpow_mul hpos.le]
      norm_num
    rw [hang, hsin, hsr, hph]
    set amp : ℝ := Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ) *
      (Real.sqrt (2 / Real.pi) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ))) / (1 - t ^ 2) ^ ((1 : ℝ) / 4) with hamp
    have hamp0 : 0 < amp := by
      have : 0 < (1 - t ^ 2) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hpos _
      rw [hamp]; positivity
    have e : Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ) *
          (Real.sqrt (2 / Real.pi) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * ((1 - t ^ 2) ^ ((1 : ℝ) / 4))⁻¹ *
            (Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4) + R)) -
        2 * (1 / 2 * (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ)) *
          (Real.sqrt (2 / Real.pi) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)))) / (1 - t ^ 2) ^ ((1 : ℝ) / 4) *
          Real.cos (μ ^ 2 * ((Real.arccos t - t * Real.sqrt (1 - t ^ 2)) / 2) - Real.pi / 4) = amp * R := by
      rw [hamp]; ring
    have e2 : 2 * (1 / 2 * (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (n.factorial : ℝ)) *
          (Real.sqrt (2 / Real.pi) * (2 * (n : ℝ) + 1) ^ (-(1 / 4 : ℝ)))) / (1 - t ^ 2) ^ ((1 : ℝ) / 4) = amp := by
      rw [hamp]; ring
    rw [e, e2, abs_mul, abs_of_pos hamp0]
    have hμi : μ⁻¹ ^ 2 = 1 / (2 * (n : ℝ) + 1) := by rw [inv_pow, hn]; simp
    rw [hμi]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hb : |R| ≤ 2 * C * (1 / (2 * (n : ℝ) + 1)) := by
      refine hR.trans ?_
      rw [div_le_iff₀ hn1]
      field_simp
      nlinarith [hC, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc amp * |R| ≤ amp * (2 * C * (1 / (2 * (n : ℝ) + 1))) := mul_le_mul_of_nonneg_left hb hamp0.le
      _ = 2 * C * (1 / (2 * (n : ℝ) + 1)) * amp := by ring


/-- **The phase fact holds for the actual function `pcU`** (DLMF 12.10.18 on the lattice `mu^2 = 2n+1`). -/
theorem pcPhaseFact : PCPhaseFact pcU where
  phase_osc := pc_phase_osc_lattice

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_phase_osc_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pc_phase_osc_lattice

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pcPhaseFact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pcPhaseFact

end FormalResearch.JacobiEigenvectors.Charts
