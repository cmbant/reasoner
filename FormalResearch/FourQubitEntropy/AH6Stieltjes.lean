import FormalResearch.FourQubitEntropy.AH6Newton

/-!
# The Stieltjes remainder identity for `g(e) = negMulLog (e/8)`

`-t ln t = ∫₀¹ t(1-t)/(t + (1-t) r) dr`, i.e. `g(e) = ∫₀¹ κ_r(e) dr` with `κ_r(e) = e(8-e)/(8 D_r(e))`,
`D_r(e) = (1-r) e + 8r` (a finite-interval form of the Stieltjes representation of the paper's eq.
`seven-joint-stieltjes`; the substitution `s = 8r/(1-r)` turns the paper's integral over `[0,∞)` into this one).
For `r < 1`, `κ_r = 1/ρ² - e/(8ρ) - (8r/ρ²)/D_r` (`ρ = 1-r`) is affine plus a multiple of `1/D_r`, so by
`phi_remainder` its Newton interpolant on the three double nodes has the remainder
`κ_r(e) - N_r(e) = -8 r ρ⁴ q(e)²/(D_r(e) D_r(n₁)² D_r(n₂)² D_r(n₃)²)` (`kap_remainder`).
-/

namespace FormalResearch.FourQubitEntropy.AH6

/-- `D_r(t) = (1-r) t + 8 r`. -/
def Dr (r t : ℝ) : ℝ := (1 - r) * t + 8 * r

/-- `κ_r(t) = t(8-t)/(8 D_r(t))`. -/
noncomputable def kap (r t : ℝ) : ℝ := t * (8 - t) / (8 * Dr r t)

/-- `∂_t κ_r(t)`. -/
noncomputable def kapd (r t : ℝ) : ℝ :=
  ((8 - 2 * t) * Dr r t - t * (8 - t) * (1 - r)) / (8 * Dr r t ^ 2)

theorem kap_decomp {r t : ℝ} (hρ : 1 - r ≠ 0) (ht : Dr r t ≠ 0) :
    kap r t = -8 * r / (1 - r) ^ 2 * (1 / Dr r t) + (1 / (1 - r) ^ 2 + (-1 / (8 * (1 - r))) * t) := by
  unfold kap
  field_simp
  unfold Dr
  ring

theorem kapd_decomp {r t : ℝ} (hρ : 1 - r ≠ 0) (ht : Dr r t ≠ 0) :
    kapd r t = -8 * r / (1 - r) ^ 2 * (-(1 - r) / (Dr r t * Dr r t)) + (-1 / (8 * (1 - r))) := by
  unfold kapd
  field_simp
  unfold Dr
  ring

section Algebra

variable {n1 n2 n3 i21 i31 i32 : ℝ}

/-- Additivity and homogeneity of `newtonP` in the data. -/
theorem newtonP_comb (c : ℝ) (v1 w1 v2 w2 v3 w3 v1' w1' v2' w2' v3' w3' e : ℝ) :
    newtonP n1 n2 n3 i21 i31 i32 (c * v1 + v1') (c * w1 + w1') (c * v2 + v2') (c * w2 + w2')
        (c * v3 + v3') (c * w3 + w3') e =
      c * newtonP n1 n2 n3 i21 i31 i32 v1 w1 v2 w2 v3 w3 e +
        newtonP n1 n2 n3 i21 i31 i32 v1' w1' v2' w2' v3' w3' e := by
  simp only [newtonP, tab, step]
  ring

/-- The Newton polynomial of affine data is the affine function. -/
theorem newtonP_affine (h21 : (n2 - n1) * i21 = 1) (h32 : (n3 - n2) * i32 = 1) (a b e : ℝ) :
    newtonP n1 n2 n3 i21 i31 i32 (a + b * n1) b (a + b * n2) b (a + b * n3) b e = a + b * e := by
  have e12 : step (a + b * n2) (a + b * n1) i21 = b := by
    unfold step; linear_combination b * h21
  have e34 : step (a + b * n3) (a + b * n2) i32 = b := by
    unfold step; linear_combination b * h32
  have z : ∀ i : ℝ, step b b i = 0 := fun i => by unfold step; ring
  have z0 : ∀ i : ℝ, step 0 0 i = 0 := fun i => by unfold step; ring
  simp only [newtonP, tab, e12, e34, z, z0]
  ring


/-- **Per-`r` Hermite remainder of `κ_r`.** -/
theorem kap_remainder {r e : ℝ} (hr : r < 1) (h21 : (n2 - n1) * i21 = 1) (h31 : (n3 - n1) * i31 = 1)
    (h32 : (n3 - n2) * i32 = 1) (hD1 : Dr r n1 ≠ 0) (hD2 : Dr r n2 ≠ 0) (hD3 : Dr r n3 ≠ 0)
    (hDe : Dr r e ≠ 0) :
    kap r e - newtonP n1 n2 n3 i21 i31 i32 (kap r n1) (kapd r n1) (kap r n2) (kapd r n2)
        (kap r n3) (kapd r n3) e =
      -8 * r * (1 - r) ^ 4 * ((e - n1) ^ 2 * (e - n2) ^ 2 * (e - n3) ^ 2) /
        (Dr r e * Dr r n1 ^ 2 * Dr r n2 ^ 2 * Dr r n3 ^ 2) := by
  have hρ : (1 - r) ≠ 0 := by intro h; linarith
  set ρ : ℝ := 1 - r with hρdef
  have hk := fun t (ht : Dr r t ≠ 0) => kap_decomp (t := t) hρ ht
  have hkd := fun t (ht : Dr r t ≠ 0) => kapd_decomp (t := t) hρ ht
  rw [hk e hDe, hk n1 hD1, hk n2 hD2, hk n3 hD3, hkd n1 hD1, hkd n2 hD2, hkd n3 hD3]
  rw [newtonP_comb, newtonP_affine h21 h32]
  have hE1 : Dr r e - Dr r n1 = ρ * (e - n1) := by unfold Dr; rw [hρdef]; ring
  have hE2 : Dr r e - Dr r n2 = ρ * (e - n2) := by unfold Dr; rw [hρdef]; ring
  have hE3 : Dr r e - Dr r n3 = ρ * (e - n3) := by unfold Dr; rw [hρdef]; ring
  have hD21 : Dr r n2 - Dr r n1 = ρ * (n2 - n1) := by unfold Dr; rw [hρdef]; ring
  have hD31 : Dr r n3 - Dr r n1 = ρ * (n3 - n1) := by unfold Dr; rw [hρdef]; ring
  have hD32 : Dr r n3 - Dr r n2 = ρ * (n3 - n2) := by unfold Dr; rw [hρdef]; ring
  have hrem := phi_remainder (ρ := ρ) hD1 hD2 hD3 hDe h21 h31 h32 hD21 hD31 hD32 hE1 hE2 hE3
  have key : -8 * r / ρ ^ 2 * (1 / Dr r e) + (1 / ρ ^ 2 + -1 / (8 * ρ) * e) -
      (-8 * r / ρ ^ 2 * newtonP n1 n2 n3 i21 i31 i32 (1 / Dr r n1) (-ρ / (Dr r n1 * Dr r n1))
        (1 / Dr r n2) (-ρ / (Dr r n2 * Dr r n2)) (1 / Dr r n3) (-ρ / (Dr r n3 * Dr r n3)) e +
        (1 / ρ ^ 2 + -1 / (8 * ρ) * e)) =
      -8 * r / ρ ^ 2 * (1 / Dr r e - newtonP n1 n2 n3 i21 i31 i32 (1 / Dr r n1)
        (-ρ / (Dr r n1 * Dr r n1)) (1 / Dr r n2) (-ρ / (Dr r n2 * Dr r n2)) (1 / Dr r n3)
        (-ρ / (Dr r n3 * Dr r n3)) e) := by ring
  rw [key, hrem]
  field_simp

end Algebra

end FormalResearch.FourQubitEntropy.AH6
