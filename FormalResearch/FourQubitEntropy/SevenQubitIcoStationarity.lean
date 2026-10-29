import FormalResearch.FourQubitEntropy.SevenQubitIcoStarBounds

/-!
# The closed equation for the family maximiser `x_*`

`prop:entropy-seven-stationarity` (`seven_qubit_entropy_local.tex`, quoted in Section "Entropy selects a
different state" of `four_qubit_entropy.tex`, `thm:fqe-seven-entropy`) states that the unique maximiser
`x_*` of the mean three-qubit entropy `E₃` on the icosahedral family is the unique root in `(0, 1/2)` of
`2³²(1 - 2x)¹⁵ = 3⁸(1 + 8x)⁸(1 + 28x)⁷`.

Proved here, from `E3d_eq_log` (the derivative of `E3` as a logarithm) and the maximiser `c` of
`E3_unique_max`, with `u = (1-2x)/30`, `3u + x = 3(1+8x)/30`, `u + x = (1+28x)/30`:

* `E3d_eq_log_ratio`: `E3d x = (4/35) log (L x / R x)` with `L x = 2³²(1-2x)¹⁵`, `R x = 3⁸(1+8x)⁸(1+28x)⁷`
  (the exponent identity `4⁵² 8⁸ = (2³²)⁴`, `3³² = (3⁸)⁴`);
* `E3d_pos_iff`, `E3d_eq_zero_iff`, `E3d_neg_iff`: the sign of the derivative is the sign of `L - R`;
* `star_equation`: the maximiser `c` satisfies the closed equation and it is the only root in `(0, 1/2)`,
  together with `1/32 < c < 37/524` (from `star_bounds`);
* `star_enclosure`: `0.0698287 < c < 0.0698288` (exact integer comparison of `L - R` at the two endpoints).

Not proved here: the full-space (`ℂP¹²⁷`) stationarity of `ψ_{x_*}`.  The paper deduces it from the family
stationary point by the symmetric-criticality lemma `lem:seven-family-symmetric-criticality`, which is not
formalized (`SevenQubitIcoContraction` has the earlier integer contraction identities for the gradient plane,
not the entropy-gradient step); the file proves only the one-parameter, within-family stationarity. The decimal value of `E₃(ψ_{x_*})` is in `SevenQubitIcoStarValue`.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

namespace Stationarity

open Real Set

/-- `L x = 2³² (1 - 2x)¹⁵`. -/
noncomputable def L (x : ℝ) : ℝ := 2 ^ 32 * (1 - 2 * x) ^ 15

/-- `R x = 3⁸ (1 + 8x)⁸ (1 + 28x)⁷`. -/
noncomputable def R (x : ℝ) : ℝ := 3 ^ 8 * (1 + 8 * x) ^ 8 * (1 + 28 * x) ^ 7

theorem L_pos {x : ℝ} (h : x < 1 / 2) : 0 < L x := by
  unfold L
  have : 0 < 1 - 2 * x := by linarith
  positivity

theorem R_pos {x : ℝ} (h : 0 ≤ x) : 0 < R x := by
  unfold R
  have h1 : 0 < 1 + 8 * x := by linarith
  have h2 : 0 < 1 + 28 * x := by linarith
  positivity

/-- The ratio inside `E3d_eq_log` is the fourth power of `L/R`. -/
theorem ratio_eq_pow {x : ℝ} :
    (4 * u x) ^ 52 * (8 * u x) ^ 8 / ((3 * u x + x) ^ 32 * (u x + x) ^ 28) = (L x / R x) ^ 4 := by
  have e1 : u x = (1 - 2 * x) / 30 := rfl
  have e2 : 3 * u x + x = 3 * (1 + 8 * x) / 30 := by rw [e1]; ring
  have e3 : u x + x = (1 + 28 * x) / 30 := by rw [e1]; ring
  rw [e2, e3, e1]
  unfold L R
  by_cases hd : (3 ^ 8 * (1 + 8 * x) ^ 8 * (1 + 28 * x) ^ 7 : ℝ) = 0
  · have h8 : (1 + 8 * x) = 0 ∨ (1 + 28 * x) = 0 := by
      rcases mul_eq_zero.mp hd with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · left; exact pow_eq_zero_iff (by norm_num) |>.mp h
      · right; exact pow_eq_zero_iff (by norm_num) |>.mp h
    rcases h8 with h | h
    · rw [h]; simp
    · rw [h]; simp
  · have h8 : (1 + 8 * x) ≠ 0 := fun h => hd (by rw [h]; simp)
    have h28 : (1 + 28 * x) ≠ 0 := fun h => hd (by rw [h]; simp)
    field_simp
    ring

/-- `E3d` as a multiple of `log (L/R)`. -/
theorem E3d_eq_log_ratio {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) :
    E3d x = (4 / 35) * log (L x / R x) := by
  rw [E3d_eq_log h0 h1, ratio_eq_pow, Real.log_pow]
  push_cast
  ring

theorem E3d_pos_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) : 0 < E3d x ↔ R x < L x := by
  rw [E3d_eq_log_ratio h0 h1]
  have hL := L_pos h1
  have hR := R_pos h0
  constructor
  · intro h
    have : 0 < log (L x / R x) := by linarith
    have := (Real.log_pos_iff (div_pos hL hR).le).mp this
    rwa [one_lt_div hR] at this
  · intro h
    have : 1 < L x / R x := (one_lt_div hR).mpr h
    have := Real.log_pos this
    positivity

theorem E3d_neg_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) : E3d x < 0 ↔ L x < R x := by
  rw [E3d_eq_log_ratio h0 h1]
  have hL := L_pos h1
  have hR := R_pos h0
  constructor
  · intro h
    have h' : log (L x / R x) < 0 := by linarith
    have := (Real.log_neg_iff (div_pos hL hR)).mp h'
    rwa [div_lt_one hR] at this
  · intro h
    have : L x / R x < 1 := (div_lt_one hR).mpr h
    have := Real.log_neg (div_pos hL hR) this
    linarith

/-- **The closed equation.** `E3d x = 0` iff `2³²(1-2x)¹⁵ = 3⁸(1+8x)⁸(1+28x)⁷`. -/
theorem E3d_eq_zero_iff {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1 / 2) : E3d x = 0 ↔ L x = R x := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := (E3d_neg_iff h0 h1).mpr hlt; linarith
    · have := (E3d_pos_iff h0 h1).mpr hgt; linarith
  · intro h
    rw [E3d_eq_log_ratio h0 h1, h, div_self (R_pos h0).ne']
    simp

/-- **`prop:entropy-seven-stationarity`, scalar part.** The maximiser `x_*` of the mean three-qubit
entropy on the icosahedral family satisfies `2³²(1-2x_*)¹⁵ = 3⁸(1+8x_*)⁸(1+28x_*)⁷`, it is the only root
of that equation in `(0, 1/2)`, and `1/32 < x_* < 37/524`. -/
theorem star_equation : ∃ c : ℝ, (∀ y ∈ Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    1 / 32 < c ∧ c < 37 / 524 ∧
    2 ^ 32 * (1 - 2 * c) ^ 15 = 3 ^ 8 * (1 + 8 * c) ^ 8 * (1 + 28 * c) ^ 7 ∧
    ∀ y : ℝ, 0 < y → y < 1 / 2 →
      2 ^ 32 * (1 - 2 * y) ^ 15 = 3 ^ 8 * (1 + 8 * y) ^ 8 * (1 + 28 * y) ^ 7 → y = c := by
  obtain ⟨c, h32, hc1, hmax, -, -⟩ := star_bounds
  have hc0 : 0 < c := by linarith
  have hz : E3d c = 0 := by
    have hloc : IsLocalMax E3 c := by
      have hnhds : Icc (0 : ℝ) (1 / 2) ∈ nhds c :=
        Icc_mem_nhds hc0 (by linarith)
      filter_upwards [hnhds] with y hy
      by_cases h : y = c
      · rw [h]
      · exact (hmax y hy h).le
    have := hloc.hasDerivAt_eq_zero (hasDerivAt_E3 hc0.le (by linarith : c < 1 / 2))
    exact this ▸ rfl
  refine ⟨c, hmax, h32, hc1, ?_, ?_⟩
  · have := (E3d_eq_zero_iff hc0.le (by linarith)).mp hz
    unfold L R at this
    exact this
  · intro y hy0 hy1 hy
    have hyz : E3d y = 0 := (E3d_eq_zero_iff hy0.le hy1).mpr (by unfold L R; exact hy)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := E3d_strictAntiOn ⟨hy0.le, hy1⟩ ⟨hc0.le, by linarith⟩ hlt
      rw [hz, hyz] at this; exact lt_irrefl _ this
    · have := E3d_strictAntiOn ⟨hc0.le, by linarith⟩ ⟨hy0.le, hy1⟩ hgt
      rw [hz, hyz] at this; exact lt_irrefl _ this

/-- The root `x_*` lies in `(0.0698287, 0.0698288)`: an exact integer comparison of `L - R` at the two
endpoints, transferred by the monotonicity of `E3d`. -/
theorem star_enclosure : ∃ c : ℝ, (∀ y ∈ Icc (0 : ℝ) (1 / 2), y ≠ c → E3 y < E3 c) ∧
    (698287 / 10000000 : ℝ) < c ∧ c < 698288 / 10000000 := by
  obtain ⟨c, hmax, h32, hc1, heq, -⟩ := star_equation
  have hc0 : 0 < c := by linarith
  have hz : E3d c = 0 := (E3d_eq_zero_iff hc0.le (by linarith)).mpr (by unfold L R; exact heq)
  refine ⟨c, hmax, ?_, ?_⟩
  · by_contra hle
    replace hle := not_lt.mp hle
    have hpos : 0 < E3d (698287 / 10000000) :=
      (E3d_pos_iff (by norm_num) (by norm_num)).mpr (by unfold L R; norm_num)
    have := E3d_strictAntiOn.antitoneOn ⟨hc0.le, by linarith⟩ ⟨by norm_num, by norm_num⟩ hle
    linarith
  · by_contra hle
    replace hle := not_lt.mp hle
    have hneg : E3d (698288 / 10000000) < 0 :=
      (E3d_neg_iff (by norm_num) (by norm_num)).mpr (by unfold L R; norm_num)
    have := E3d_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩ ⟨hc0.le, by linarith⟩ hle
    linarith

end Stationarity

end FormalResearch.FourQubitEntropy.SevenQubitIco
