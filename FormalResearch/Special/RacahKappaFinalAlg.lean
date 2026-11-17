module

public import Mathlib

/-!
# The final real algebra of the sharp-constant mass accounting (Racah / Hahn closed form)

Quantities: `T = (κ² + μ²)δ/2` (target `T → 1`), `M` the Gauss weight with `M δ³ √s = 1`, the left mass `L ≤ εM`, the band mass `B ∈ [T M (1 - a_B - θ), T M (1 + θ)]`,
the zone mass `Z ≤ A₀ (2κ² + 2)/δ² + K₃ (2κ² + 2)/δ`, `M = L + B + Z`.  `rk_final_alg`: with all error terms `≤ u` (`u ≤ 1/6`) one gets `|κ²δ - 2| ≤ 40 u`.

**Claim class: proved** (real algebra).
-/

@[expose] public section

namespace FormalResearch.Special

/-- `T (1 - w) ≤ 1`, `1 ≤ ε + T(1+θ) + Tζ + ξ`, `w ≤ 1/2`: `|T - 1| ≤ 2(w + ε + ξ + θ + ζ)`. -/
lemma rk_alg {T w ε ξ θ ζ : ℝ} (hT : 0 ≤ T) (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) (hε : 0 ≤ ε) (hξ : 0 ≤ ξ) (hθ : 0 ≤ θ) (hζ : 0 ≤ ζ)
    (hu : T * (1 - w) ≤ 1) (hl : 1 ≤ ε + T * (1 + θ) + T * ζ + ξ) : |T - 1| ≤ 2 * (w + ε + ξ + θ + ζ) := by
  have hT2 : T ≤ 2 := by nlinarith
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hT2 hθ, mul_le_mul_of_nonneg_right hT2 hζ]
  · nlinarith [mul_le_mul_of_nonneg_right hT2 hw0]

/-- The zone mass in units of `M`: `Z ≤ (Tζ + ξ) M`. -/
lemma rk_zone_unit {κ μ δ M sq Z A0 K3 : ℝ} (hδ : 0 < δ) (hsq : 0 < sq) (hM0 : 0 < M) (hMe : M = 1 / (δ ^ 3 * sq))
    (hZ : Z ≤ A0 * (2 * κ ^ 2 + 2) / δ ^ 2 + K3 * (2 * κ ^ 2 + 2) / δ) (hA0 : 0 ≤ A0) (hK3 : 0 ≤ K3) :
    Z ≤ ((κ ^ 2 + μ ^ 2) * δ / 2 * (4 * sq * (A0 + K3 * δ)) + 2 * sq * δ * (A0 + K3 * δ)) * M := by
  set R2 : ℝ := κ ^ 2 + μ ^ 2 with hR2
  set T : ℝ := R2 * δ / 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hκδ : κ ^ 2 * δ ≤ 2 * T := by
    have : κ ^ 2 ≤ R2 := by rw [hR2]; nlinarith [sq_nonneg μ]
    rw [hT]; nlinarith
  have h1 : Z * (δ ^ 3 * sq) ≤ T * (4 * sq * (A0 + K3 * δ)) + 2 * sq * δ * (A0 + K3 * δ) := by
    have hz1 : Z * (δ ^ 3 * sq) ≤ (A0 * (2 * κ ^ 2 + 2) / δ ^ 2 + K3 * (2 * κ ^ 2 + 2) / δ) * (δ ^ 3 * sq) :=
      mul_le_mul_of_nonneg_right hZ (by positivity)
    have e : (A0 * (2 * κ ^ 2 + 2) / δ ^ 2 + K3 * (2 * κ ^ 2 + 2) / δ) * (δ ^ 3 * sq) =
        sq * (A0 * ((2 * κ ^ 2 + 2) * δ) + K3 * δ * ((2 * κ ^ 2 + 2) * δ)) := by
      field_simp
    rw [e] at hz1
    have hk : (2 * κ ^ 2 + 2) * δ ≤ 4 * T + 2 * δ := by nlinarith
    have h2 : sq * (A0 * ((2 * κ ^ 2 + 2) * δ) + K3 * δ * ((2 * κ ^ 2 + 2) * δ)) ≤
        sq * (A0 * (4 * T + 2 * δ) + K3 * δ * (4 * T + 2 * δ)) := by
      apply mul_le_mul_of_nonneg_left _ hsq.le
      have := mul_le_mul_of_nonneg_left hk hA0
      have := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ K3 * δ)
      linarith
    have e2 : sq * (A0 * (4 * T + 2 * δ) + K3 * δ * (4 * T + 2 * δ)) =
        T * (4 * sq * (A0 + K3 * δ)) + 2 * sq * δ * (A0 + K3 * δ) := by ring
    linarith
  have : Z = Z * (δ ^ 3 * sq) * M := by
    rw [hMe]; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h1 hM0.le

/-- **The final algebra.** -/
lemma rk_final_alg {κ μ δ M sq L B Z aB θ ε A0 K3 u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsq : 0 < sq) (hM : M * δ ^ 3 * sq = 1)
    (hL0 : 0 ≤ L) (hLε : L ≤ ε * M) (hZ0 : 0 ≤ Z) (hsum : M = L + B + Z)
    (hBlo : (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 - aB - θ) ≤ B) (hBhi : B ≤ (κ ^ 2 + μ ^ 2) * δ / 2 * M * (1 + θ))
    (hZ : Z ≤ A0 * (2 * κ ^ 2 + 2) / δ ^ 2 + K3 * (2 * κ ^ 2 + 2) / δ) (hμ : |μ| ≤ δ ^ 3)
    (hA0 : 0 ≤ A0) (hK3 : 0 ≤ K3) (haB0 : 0 ≤ aB) (hθ0 : 0 ≤ θ) (hε0 : 0 ≤ ε) (hu6 : u ≤ 1 / 6)
    (hζ : 4 * sq * (A0 + K3 * δ) ≤ u) (hξ : 2 * sq * δ * (A0 + K3 * δ) ≤ u) (haB : aB ≤ 2 * u) (hθ : θ ≤ u) (hε : ε ≤ u)
    (hδu : δ ≤ 8 * u) : |κ ^ 2 * δ - 2| ≤ 40 * u := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hMe : M = 1 / (δ ^ 3 * sq) := by
    have : δ ^ 3 * sq ≠ 0 := by positivity
    field_simp; linarith
  have hM0 : 0 < M := by rw [hMe]; positivity
  set R2 : ℝ := κ ^ 2 + μ ^ 2 with hR2
  set T : ℝ := R2 * δ / 2 with hT
  have hT0 : 0 ≤ T := by positivity
  have hBM : B ≤ M := by linarith
  have hu1 : T * (1 - (aB + θ)) ≤ 1 := by
    have h1 : T * M * (1 - aB - θ) ≤ M := hBlo.trans hBM
    have h2 : (T * (1 - (aB + θ))) * M ≤ 1 * M := by
      have : T * M * (1 - aB - θ) = (T * (1 - (aB + θ))) * M := by ring
      linarith
    exact le_of_mul_le_mul_right h2 hM0
  have hZM : Z ≤ (T * (4 * sq * (A0 + K3 * δ)) + 2 * sq * δ * (A0 + K3 * δ)) * M :=
    rk_zone_unit hδ hsq hM0 hMe hZ hA0 hK3
  set ζ : ℝ := 4 * sq * (A0 + K3 * δ) with hζdef
  set ξ : ℝ := 2 * sq * δ * (A0 + K3 * δ) with hξdef
  have hl : 1 ≤ ε + T * (1 + θ) + T * ζ + ξ := by
    have h1 : M ≤ ε * M + T * M * (1 + θ) + (T * ζ + ξ) * M := by linarith
    have h2 : 1 * M ≤ (ε + T * (1 + θ) + T * ζ + ξ) * M := by
      have e : (ε + T * (1 + θ) + T * ζ + ξ) * M = ε * M + T * M * (1 + θ) + (T * ζ + ξ) * M := by ring
      rw [e]; linarith
    exact le_of_mul_le_mul_right h2 hM0
  have hζ0 : 0 ≤ ζ := by positivity
  have hξ0 : 0 ≤ ξ := by positivity
  have hmain := rk_alg (w := aB + θ) hT0 (by positivity) (by linarith) hε0 hξ0 hθ0 hζ0 hu1 hl
  have hμ2 : μ ^ 2 * δ ≤ δ := by
    have h1 : μ ^ 2 ≤ 1 := by
      have : |μ| ≤ 1 := hμ.trans (pow_le_one₀ hδ.le hδ1)
      nlinarith [abs_nonneg μ, sq_abs μ]
    nlinarith
  have hk2 : κ ^ 2 * δ = 2 * T - μ ^ 2 * δ := by rw [hT, hR2]; ring
  rw [abs_le] at hmain ⊢
  obtain ⟨hm1, hm2⟩ := hmain
  constructor
  · have := mul_nonneg (sq_nonneg μ) hδ.le
    linarith only [hk2, hm1, hm2, hμ2, this, hδu, haB, hθ, hε, hζ, hξ, hζdef, hξdef, this]
  · have := mul_nonneg (sq_nonneg μ) hδ.le
    linarith only [hk2, hm1, hm2, hμ2, this, hδu, haB, hθ, hε, hζ, hξ, hζdef, hξdef]

/-- info: 'FormalResearch.Special.rk_final_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rk_final_alg

end FormalResearch.Special
