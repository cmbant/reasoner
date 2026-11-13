module

public import FormalResearch.Racah.P2ThreeJSeed

/-!
# Central factorial products as polynomials in `t = h²` (Weyl P2, `lem:centeredshift`)

`Ct r u t` is the central product `𝔠_r(u,h) = ∏_{q=-(r-1)/2}^{(r-1)/2} (u+qh)` written as a
function of `t = h²`: pairing the factors `q, -q` gives
`Ct 0 = 1`, `Ct 1 = u`, `Ct (r+2) = (u² - ((r+1)²/4) t) Ct r`.
`Cprod_eq_Ct` identifies it with the repository's `Cprod` at `t = h²`; this is the interface
used by the analytic half of P2 (the dependence on `h` is through `h²` only).
-/

@[expose] public section

namespace FormalResearch.Racah

/-- The central product `𝔠_r(u,h)` as a polynomial function of `t = h²`. -/
noncomputable def Ct : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, u, _ => u
  | r + 2, u, t => (u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t) * Ct r u t

lemma Ct_zero (u t : ℝ) : Ct 0 u t = 1 := rfl

lemma Ct_one (u t : ℝ) : Ct 1 u t = u := rfl

lemma Ct_succ_succ (r : ℕ) (u t : ℝ) :
    Ct (r + 2) u t = (u ^ 2 - ((r : ℝ) + 1) ^ 2 / 4 * t) * Ct r u t := rfl

/-- `𝔠_r(u,h) = Ct r u (h²)`. -/
theorem Cprod_eq_Ct (r : ℕ) (u h : ℝ) : Cprod r u h = Ct r u (h ^ 2) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Cprod_zero, Ct_zero]
    | 1, _ => simp [Cprod_one, Ct_one]
    | r + 2, ih =>
      rw [Cprod_succ_succ, Ct_succ_succ, ih r (by omega)]
      ring

/-- At `t = 0` the central product is the plain power: `Ct r u 0 = u ^ r`. -/
theorem Ct_zero_t (r : ℕ) (u : ℝ) : Ct r u 0 = u ^ r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simp [Ct_zero]
    | 1, _ => simp [Ct_one]
    | r + 2, ih => rw [Ct_succ_succ, ih r (by omega)]; ring

end FormalResearch.Racah
