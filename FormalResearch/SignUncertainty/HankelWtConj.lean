module

public import FormalResearch.SignUncertainty.HankelLocalHolo
public import FormalResearch.SignUncertainty.HankelLangerReal

/-!
# Complex-conjugation symmetry of `W̃_c` and reality of the local density (`gt:7.7c`, M5-c)

For real `f`, `0 < c`:

* `hankelMellinStrip_conj`: `M̃_f(conj z) = conj M̃_f(z)` for every `z` (the Mellin integral of a real
  function, `Complex.Gamma_conj`, `Complex.cpow_conj` on positive real bases).
* `hankelHLog_conj`, `hankelHInt_conj`: `ℋ(conj ζ) = conj ℋ(ζ)` on `0 ≤ Re ζ < 1` (through the Binet
  branch `hLog` and `binetLogGamma`, whose conjugation symmetry is proved here from `lap_conj`).
* `hankelWt_conj`: `W̃_c(conj ζ) = conj W̃_c(ζ)` on `0 < Re ζ < 1`.
* `hankelJ_conj`: `J(ℓ, conj ζ) = conj J(ℓ, ζ)` at real `ℓ`, `0 < Re ζ < 1`.
* `hankelLocal_im_eq_zero`: the local density `hankelLocal c f ℓ` is real for real `ℓ`.

Proof status and provenance: `hankelMellinStrip_conj`, `hankelBinetRem_conj`, `hankelBinetDiff_conj`,
`hankelBinetLogGamma_conj`, `hankelSSer_conj` and `hankelLocPhi_conj` are new small lemmas whose
proofs are the conjugation computations of `mellinK0_conj` and `stripG_conj` (`LobeSaddleCore`) written
out for these objects; they restate no Mathlib lemma beyond the `Complex.*` and `integral_conj` rewrites
they use. `hankelWt_conj`, `hankelJ_conj`, `hankelLocal_im_eq_zero` are the assembled statements.
Only `f` real is used: `IsHankelEigenfn` is not assumed, and neither `0 < c` nor `‖ζ‖ < 1` is needed (the
statements are formal identities valid for every real `c` and every `ζ` with `0 < Re ζ < 1`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling FormalResearch.Asymptotics FormalResearch.CohnElkies

/-- Conjugation of the Mellin strip function of a real `f`: `M̃_f(conj z) = conj M̃_f(z)`. -/
theorem hankelMellinStrip_conj (f : ℝ → ℝ) (z : ℂ) :
    mellinStrip f (starRingEnd ℂ z) = starRingEnd ℂ (mellinStrip f z) := by
  have hA : ((2 * Real.pi : ℝ) : ℂ) ^ (starRingEnd ℂ z) =
      starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) ^ z) := by
    have harg : (((2 * Real.pi : ℝ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm
    have h := Complex.cpow_conj _ z harg
    rwa [Complex.conj_ofReal] at h
  have hR : mellinRaw f (starRingEnd ℂ z) = starRingEnd ℂ (mellinRaw f z) := by
    unfold mellinRaw
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    have hΔ0 : 0 < Δ := mem_Ioi.mp hΔ
    have harg : (((Δ : ℝ)) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hΔ0.le]
      exact Real.pi_ne_zero.symm
    have hc : ((Δ : ℝ) : ℂ) ^ (starRingEnd ℂ z - 1) = starRingEnd ℂ (((Δ : ℝ) : ℂ) ^ (z - 1)) := by
      have h := Complex.cpow_conj _ (z - 1) harg
      rw [Complex.conj_ofReal, map_sub, map_one] at h
      exact h
    rw [map_mul, Complex.conj_ofReal, hc]
  unfold mellinStrip
  rw [hA, Complex.Gamma_conj, hR, map_mul, map_div₀]

/-- Conjugation of the Binet remainder kernel integral: `B_Bin(conj w) = conj B_Bin(w)`. -/
lemma hankelBinetRem_conj (w : ℂ) : binetRem (starRingEnd ℂ w) = starRingEnd ℂ (binetRem w) := by
  unfold binetRem
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]

/-- `B_c(conj ζ) = conj B_c(ζ)` for real `c`. -/
lemma hankelBinetDiff_conj (c : ℝ) (ζ : ℂ) :
    binetDiff c (starRingEnd ℂ ζ) = starRingEnd ℂ (binetDiff c ζ) := by
  have hcR : binetRem (c : ℂ) = starRingEnd ℂ (binetRem (c : ℂ)) := by
    rw [← hankelBinetRem_conj, Complex.conj_ofReal]
  unfold binetDiff
  rw [show (c : ℂ) * (1 - starRingEnd ℂ ζ) = starRingEnd ℂ ((c : ℂ) * (1 - ζ)) by
    rw [map_mul, map_sub, map_one, Complex.conj_ofReal], hankelBinetRem_conj, map_sub, ← hcR]

/-- Conjugation symmetry of `binetLogGamma` on `Re z > 0`. -/
lemma hankelBinetLogGamma_conj {z : ℂ} (hz : 0 < z.re) :
    binetLogGamma (starRingEnd ℂ z) = starRingEnd ℂ (binetLogGamma z) := by
  have harg : z.arg ≠ Real.pi := by
    have h := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))).2
    exact ne_of_lt (by linarith [Real.pi_pos])
  have hB : binetB (starRingEnd ℂ z) = starRingEnd ℂ (binetB z) := lap_conj z
  unfold binetLogGamma
  rw [Complex.log_conj _ harg, hB]
  simp only [map_add, map_sub, map_mul, map_div₀, Complex.conj_ofReal, map_one, map_ofNat]

/-- `hLog` commutes with conjugation on the strip `-1 < Re z < 2`. -/
lemma hankelHLog_conj {z : ℂ} (hz : z ∈ hStrip) :
    hLog (starRingEnd ℂ z) = starRingEnd ℂ (hLog z) := by
  obtain ⟨hz1, hz2⟩ := hz
  have hhalf : ∀ a : ℂ, (a / 2).re = a.re / 2 := fun a => by simp
  have h1 : 0 < ((1 + z) / 2).re := by rw [hhalf]; simp; linarith
  have h2 : 0 < ((3 - z) / 2).re := by rw [hhalf]; simp; linarith
  have h3 : 0 < ((2 + z) / 2).re := by rw [hhalf]; simp; linarith
  have h4 : 0 < ((2 - z) / 2).re := by rw [hhalf]; simp; linarith
  have e1 : (1 + starRingEnd ℂ z) / 2 = starRingEnd ℂ ((1 + z) / 2) := by
    simp only [map_div₀, map_add, map_one, map_ofNat]
  have e2 : (3 - starRingEnd ℂ z) / 2 = starRingEnd ℂ ((3 - z) / 2) := by
    simp only [map_div₀, map_sub, map_ofNat]
  have e3 : (2 + starRingEnd ℂ z) / 2 = starRingEnd ℂ ((2 + z) / 2) := by
    simp only [map_div₀, map_add, map_ofNat]
  have e4 : (2 - starRingEnd ℂ z) / 2 = starRingEnd ℂ ((2 - z) / 2) := by
    simp only [map_div₀, map_sub, map_ofNat]
  unfold hLog
  rw [e1, e2, e3, e4, hankelBinetLogGamma_conj h1, hankelBinetLogGamma_conj h2,
    hankelBinetLogGamma_conj h3, hankelBinetLogGamma_conj h4]
  simp only [map_add, map_sub]

/-- `ℋ(conj ζ) = conj ℋ(ζ)` on `0 ≤ Re ζ < 1`. -/
theorem hankelHInt_conj {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) :
    hInt (starRingEnd ℂ ζ) = starRingEnd ℂ (hInt ζ) := by
  have hζS : ζ ∈ hStrip := ⟨by linarith, by linarith⟩
  unfold hInt
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have hm : (s : ℂ) * ζ ∈ hStrip := smul_mem_hStrip hζS ⟨hs.1.le, hs.2⟩
  have hc : starRingEnd ℂ ((s : ℂ) * ζ) = (s : ℂ) * starRingEnd ℂ ζ := by
    rw [map_mul, Complex.conj_ofReal]
  rw [map_mul, ← hankelHLog_conj hm, hc]

/-- `W̃_c(conj ζ) = conj W̃_c(ζ)` on `0 < Re ζ < 1`. -/
theorem hankelWt_conj {c : ℝ} (f : ℝ → ℝ) {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    hankelWt c f (starRingEnd ℂ ζ) = starRingEnd ℂ (hankelWt c f ζ) := by
  have e1 : (c : ℂ) * (1 - starRingEnd ℂ ζ) = starRingEnd ℂ ((c : ℂ) * (1 - ζ)) := by
    rw [map_mul, map_sub, map_one, Complex.conj_ofReal]
  unfold hankelWt
  rw [hankelHInt_conj h0.le h1, e1, hankelMellinStrip_conj, map_mul, ← Complex.exp_conj, map_neg,
    map_mul, Complex.conj_ofReal]

/-- `Φ(ℓ; conj ζ) = conj Φ(ℓ; ζ)` at real `ℓ`, since `SSer` has real coefficients. -/
lemma hankelLocPhi_conj (ℓ : ℝ) (ζ : ℂ) :
    hankelLocPhi (ℓ : ℂ) (starRingEnd ℂ ζ) = starRingEnd ℂ (hankelLocPhi (ℓ : ℂ) ζ) := by
  have hS : ∀ w : ℂ, SSer etaC (starRingEnd ℂ w) = starRingEnd ℂ (SSer etaC w) := by
    intro w
    unfold SSer
    simp only [map_mul, map_pow]
    rw [← psW_conj]
    simp only [map_pow]
  unfold hankelLocPhi
  rw [hS, map_add, map_mul, Complex.conj_ofReal]

/-- Conjugation symmetry of the local integrand `J` at real `ℓ`, `0 < Re ζ < 1`. -/
theorem hankelJ_conj {c : ℝ} (f : ℝ → ℝ) {ℓ : ℝ} {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1) :
    hankelJ c f (ℓ : ℂ) (starRingEnd ℂ ζ) = starRingEnd ℂ (hankelJ c f (ℓ : ℂ) ζ) := by
  have hz1 : 0 < (1 - ζ).re := by simp [h1]
  have harg : (1 - ζ).arg ≠ Real.pi := by
    have h := (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz1))).2
    exact ne_of_lt (by linarith [Real.pi_pos])
  have hp : (1 - starRingEnd ℂ ζ) ^ (-(1 / 2 : ℂ)) = starRingEnd ℂ ((1 - ζ) ^ (-(1 / 2 : ℂ))) := by
    have hn2 : starRingEnd ℂ (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
      simp only [map_neg, map_div₀, map_one, map_ofNat]
    have h := Complex.conj_cpow (1 - ζ) (-(1 / 2 : ℂ)) harg
    rw [hn2, map_sub, map_one] at h
    exact h
  unfold hankelJ
  rw [hp, hankelBinetDiff_conj, hankelLocPhi_conj, hankelWt_conj f h0 h1]
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal]

/-- **Reality of the local density** (`gt:7.7c`): `hankelLocal c f ℓ` is real for real `ℓ`.
The integrand satisfies `J(conj ζ) = conj J(ζ)` on the segment `1/10 + iτ`, `|τ| ≤ 1/3`, so the
integral over the symmetric interval is invariant under conjugation. -/
theorem hankelLocal_im_eq_zero {c : ℝ} (f : ℝ → ℝ) (ℓ : ℝ) :
    (hankelLocal c f (ℓ : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold hankelLocal
  have hab : -(1 / 3 : ℝ) ≤ 1 / 3 := by norm_num
  have hconj : starRingEnd ℂ (∫ τ in (-(1 / 3 : ℝ))..(1 / 3),
      hankelJ c f (ℓ : ℂ) (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) =
      ∫ τ in (-(1 / 3 : ℝ))..(1 / 3),
        starRingEnd ℂ (hankelJ c f (ℓ : ℂ) (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, integral_conj]
  have hpt : ∫ τ in (-(1 / 3 : ℝ))..(1 / 3),
      starRingEnd ℂ (hankelJ c f (ℓ : ℂ) (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) =
      ∫ τ in (-(1 / 3 : ℝ))..(1 / 3),
        hankelJ c f (ℓ : ℂ) (((1 / 10 : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le hab] at hτ
    have hτa : |τ| ≤ 1 / 3 := abs_le.mpr ⟨hτ.1, hτ.2⟩
    have hre : (0 : ℝ) < (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re := by simp
    have hre1 : (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re < 1 := by simp; norm_num
    have key := hankelJ_conj (c := c) f (ℓ := ℓ) hre hre1
    rw [← key]
    congr 1
    apply Complex.ext <;> simp
  have hneg := intervalIntegral.integral_comp_neg (a := -(1 / 3 : ℝ)) (b := 1 / 3)
    (fun τ : ℝ => hankelJ c f (ℓ : ℂ) (((1 / 10 : ℝ) : ℂ) + (τ : ℂ) * Complex.I))
  simp only [neg_neg] at hneg
  rw [hconj, hpt, hneg]

/-- info: 'FormalResearch.SignUncertainty.hankelMellinStrip_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelMellinStrip_conj

/-- info: 'FormalResearch.SignUncertainty.hankelHInt_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHInt_conj

/-- info: 'FormalResearch.SignUncertainty.hankelWt_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWt_conj

/-- info: 'FormalResearch.SignUncertainty.hankelJ_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelJ_conj

/-- info: 'FormalResearch.SignUncertainty.hankelLocal_im_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelLocal_im_eq_zero

end FormalResearch.SignUncertainty
