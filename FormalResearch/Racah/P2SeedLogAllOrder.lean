module

public import FormalResearch.Racah.P2CtLogSeries
public import FormalResearch.Asymptotics.GeometricExpansion
public import FormalResearch.Asymptotics.ExpExpansion

/-!
# All-order logarithm of the extremal `3j` seed ratio (Weyl P2, `eq:3jseedlogallorder`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, appendix `app:3j-allorder`
(`eq:3jseedlogallorder`).  Here `α = M-σ`, `β = M+σ` are natural numbers (so `2M+1 = α+β+1`),
`u_∓ = (1∓x)/2`, `t = N⁻²`.

* `seedRatio α β x t = √(𝔠_α(u₋) 𝔠_β(u₊)) / √(𝔠_{α+β+1}(1)) / √(u₋^α u₊^β)`, where
  `𝔠_r(u) = Ct r u t`.  By `eq:3jseed` and `d^M_{Mσ} = ε √((2M)!/(α!β!)) √(u₋^α u₊^β)` this is
  `Φ_M^{M,σ}/d^M_{M,σ}` on the physical lattice (`P2SeedLogAllOrderPhys`).
* `seedEll α β r x` is the paper's `ℓ_r(x) = (1/4r)[S_{2r}(2M+1) - S_{2r}(M+σ)/u₊^{2r} -
  S_{2r}(M-σ)/u₋^{2r}]` (`S_{2r}(p) = centeredPowerSum p (2r)`, which equals
  `2B_{2r+1}((p+1)/2)/(2r+1)`; `FormalResearch.Asymptotics.centeredPowerSum_even_eq_bernoulliFun`).

## Results (all proved)

* `seedRatio_log_hasSum`: **exact**: `log seedRatio α β x t = ∑_{r≥1} ℓ_r(x) t^r` as a convergent
  series, whenever `SeedOK` holds (`u_± > 0`, `t ≥ 0`, `α² t ≤ 4u₋²`, `β² t ≤ 4u₊²`,
  `(α+β+1)² t ≤ 4`, which make every factor of the central products positive).
* `seedRatio_log_hasUniformExpansion`: the same series is a uniform asymptotic expansion in
  `t → 0⁺`, uniformly for `x` in `{δ ≤ u_±}` (any compact `K ⊆ (-1,1)`:
  `seedRatio_log_hasUniformExpansion_compact`).
* `seedRatio_hasUniformExpansion`: `seedRatio` itself has the uniform expansion `∑ κ_r(x) t^r`,
  `κ_r = [t^r] exp(∑_{s≥1} ℓ_s t^s)` (`expCoeff`; formal exponential of the series).

Not covered here: the identification with `Φ_M^{Mσ}/d^M_{Mσ}` (that is `P2SeedLogAllOrderPhys`),
and the (separate, unproved here) statement that `ψ_{2r}` of the local calculus equals `κ_r`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Asymptotics Finset Filter Topology

/-- The extremal seed ratio `Φ_M^{Mσ}/d^M_{Mσ}` as a function of `(x, t)`, `t = N⁻²`
(`α = M-σ`, `β = M+σ`, `u_∓ = (1∓x)/2`). -/
noncomputable def seedRatio (α β : ℕ) (x t : ℝ) : ℝ :=
  Real.sqrt (Ct α ((1 - x) / 2) t * Ct β ((1 + x) / 2) t) / Real.sqrt (Ct (α + β + 1) 1 t) /
    Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β)

/-- The paper's `ℓ_r(x) = (1/4r)[S_{2r}(2M+1) - S_{2r}(M+σ)/u₊^{2r} - S_{2r}(M-σ)/u₋^{2r}]`
with `α = M-σ`, `β = M+σ`, `2M+1 = α+β+1`; `ℓ_0 = 0`. -/
noncomputable def seedEll (α β r : ℕ) (x : ℝ) : ℝ :=
  1 / (4 * r) * (centeredPowerSum (α + β + 1) (2 * r) -
    centeredPowerSum α (2 * r) / ((1 - x) / 2) ^ (2 * r) -
    centeredPowerSum β (2 * r) / ((1 + x) / 2) ^ (2 * r))

@[simp] theorem seedEll_zero (α β : ℕ) (x : ℝ) : seedEll α β 0 x = 0 := by simp [seedEll]

/-- The first coefficient: `ℓ_1(x) = (1/48)[P(P²-1) - α(α²-1)/u₋² - β(β²-1)/u₊²]`, `P = α+β+1`
(from `S_2(p) = p(p²-1)/12`). -/
theorem seedEll_one (α β : ℕ) (x : ℝ) :
    seedEll α β 1 x = 1 / 4 * (((α + β + 1 : ℕ) : ℝ) * (((α + β + 1 : ℕ) : ℝ) ^ 2 - 1) / 12 -
      (α : ℝ) * ((α : ℝ) ^ 2 - 1) / 12 / ((1 - x) / 2) ^ 2 -
      (β : ℝ) * ((β : ℝ) ^ 2 - 1) / 12 / ((1 + x) / 2) ^ 2) := by
  simp only [seedEll, Nat.cast_one, mul_one, centeredPowerSum_two]

/-- Hypotheses under which the seed ratio is a positive number given by convergent series. -/
structure SeedOK (α β : ℕ) (x t : ℝ) : Prop where
  hm : 0 < (1 - x) / 2
  hp : 0 < (1 + x) / 2
  ht : 0 ≤ t
  hα : (α : ℝ) ^ 2 * t ≤ 4 * ((1 - x) / 2) ^ 2
  hβ : (β : ℝ) ^ 2 * t ≤ 4 * ((1 + x) / 2) ^ 2
  hP : ((α + β + 1 : ℕ) : ℝ) ^ 2 * t ≤ 4 * 1 ^ 2

theorem SeedOK.pos {α β : ℕ} {x t : ℝ} (h : SeedOK α β x t) : 0 < seedRatio α β x t := by
  unfold seedRatio
  have h1 := Ct_pos_le α h.hm h.ht h.hα
  have h2 := Ct_pos_le β h.hp h.ht h.hβ
  have h3 := Ct_pos_le (α + β + 1) one_pos h.ht h.hP
  have h4 : 0 < ((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β := mul_pos (pow_pos h.hm _) (pow_pos h.hp _)
  positivity

/-- **`eq:3jseedlogallorder`, exact form.**  Under `SeedOK`,
`log seedRatio α β x t = ∑_{r≥1} ℓ_r(x) t^r` (convergent). -/
theorem seedRatio_log_hasSum {α β : ℕ} {x t : ℝ} (h : SeedOK α β x t) :
    HasSum (fun r : ℕ => seedEll α β r x * t ^ r) (Real.log (seedRatio α β x t)) := by
  have h1 := Ct_log_hasSum α h.hm h.ht h.hα
  have h2 := Ct_log_hasSum β h.hp h.ht h.hβ
  have h3 := Ct_log_hasSum (α + β + 1) one_pos h.ht h.hP
  have c1 := Ct_pos_le α h.hm h.ht h.hα
  have c2 := Ct_pos_le β h.hp h.ht h.hβ
  have c3 := Ct_pos_le (α + β + 1) one_pos h.ht h.hP
  have hlog : Real.log (seedRatio α β x t) =
      1 / 2 * ((Real.log (Ct α ((1 - x) / 2) t) - α * Real.log ((1 - x) / 2) +
        (Real.log (Ct β ((1 + x) / 2) t) - β * Real.log ((1 + x) / 2))) -
        (Real.log (Ct (α + β + 1) 1 t) - ((α + β + 1 : ℕ) : ℝ) * Real.log 1)) := by
    unfold seedRatio
    have hC : 0 < ((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β :=
      mul_pos (pow_pos h.hm _) (pow_pos h.hp _)
    have sA : 0 < Real.sqrt (Ct α ((1 - x) / 2) t * Ct β ((1 + x) / 2) t) :=
      Real.sqrt_pos.2 (mul_pos c1 c2)
    have sB : 0 < Real.sqrt (Ct (α + β + 1) 1 t) := Real.sqrt_pos.2 c3
    have sC : 0 < Real.sqrt (((1 - x) / 2) ^ α * ((1 + x) / 2) ^ β) := Real.sqrt_pos.2 hC
    rw [Real.log_div (div_pos sA sB).ne' sC.ne', Real.log_div sA.ne' sB.ne',
      Real.log_sqrt (mul_pos c1 c2).le, Real.log_sqrt c3.le, Real.log_sqrt hC.le,
      Real.log_mul c1.ne' c2.ne', Real.log_mul (pow_pos h.hm _).ne' (pow_pos h.hp _).ne',
      Real.log_pow, Real.log_pow]
    simp
    ring
  rw [hlog]
  have H := (((h1.add h2).sub h3).mul_left (1 / 2))
  have key : ∀ n : ℕ, seedEll α β (n + 1) x * t ^ (n + 1) = 1 / 2 *
      (-(1 / 2) * (centeredPowerSum α (2 * (n + 1)) * (t / ((1 - x) / 2) ^ 2) ^ (n + 1) /
          ((n : ℝ) + 1)) +
        -(1 / 2) * (centeredPowerSum β (2 * (n + 1)) * (t / ((1 + x) / 2) ^ 2) ^ (n + 1) /
          ((n : ℝ) + 1)) -
        -(1 / 2) * (centeredPowerSum (α + β + 1) (2 * (n + 1)) * (t / 1 ^ 2) ^ (n + 1) /
          ((n : ℝ) + 1))) := by
    intro n
    have hu1 : ((1 - x) / 2) ^ (2 * (n + 1)) ≠ 0 := (pow_pos h.hm _).ne'
    have hu2 : ((1 + x) / 2) ^ (2 * (n + 1)) ≠ 0 := (pow_pos h.hp _).ne'
    simp only [seedEll, div_pow, one_pow, ← pow_mul]
    push_cast
    field_simp
    ring
  have H' : HasSum (fun n : ℕ => seedEll α β (n + 1) x * t ^ (n + 1))
      (1 / 2 * ((Real.log (Ct α ((1 - x) / 2) t) - α * Real.log ((1 - x) / 2) +
        (Real.log (Ct β ((1 + x) / 2) t) - β * Real.log ((1 + x) / 2))) -
        (Real.log (Ct (α + β + 1) 1 t) - ((α + β + 1 : ℕ) : ℝ) * Real.log 1))) := by
    convert H using 1
    funext n
    exact key n
  refine (hasSum_nat_add_iff' 1).1 ?_
  simpa using H'

/-! ### Uniform expansions -/

/-- `|S_{2r}(p)/u^{2r}| ≤ P (P/(2δ))^{2r}` for `p ≤ P` and `0 < δ ≤ u`. -/
theorem abs_centeredPowerSum_div_le {p P : ℕ} (hpP : p ≤ P) {u δ : ℝ} (hδ : 0 < δ) (hu : δ ≤ u)
    (r : ℕ) :
    |centeredPowerSum p (2 * r) / u ^ (2 * r)| ≤ P * ((P : ℝ) / (2 * δ)) ^ (2 * r) := by
  have hu0 : 0 < u := lt_of_lt_of_le hδ hu
  rw [abs_div, abs_of_pos (pow_pos hu0 _)]
  have hpP' : (p : ℝ) ≤ P := by exact_mod_cast hpP
  calc |centeredPowerSum p (2 * r)| / u ^ (2 * r)
      ≤ |centeredPowerSum p (2 * r)| / δ ^ (2 * r) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hδ _) (pow_le_pow_left₀ hδ.le hu _)
    _ ≤ (p * ((p : ℝ) / 2) ^ (2 * r)) / δ ^ (2 * r) :=
        div_le_div_of_nonneg_right (abs_centeredPowerSum_le p _) (pow_pos hδ _).le
    _ = p * ((p : ℝ) / (2 * δ)) ^ (2 * r) := by
        rw [div_pow, div_pow, mul_pow]; field_simp
    _ ≤ P * ((P : ℝ) / (2 * δ)) ^ (2 * r) := by
        refine mul_le_mul hpP' (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
          (Nat.cast_nonneg P)
        exact div_le_div_of_nonneg_right hpP' (by positivity)

/-- The geometric ratio controlling the coefficients of the `x`-uniform expansion. -/
noncomputable def seedQ (α β : ℕ) (δ : ℝ) : ℝ := (((α + β + 1 : ℕ) : ℝ) / (2 * δ)) ^ 2

theorem abs_seedEll_le (α β : ℕ) {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : δ ≤ (1 - x) / 2 ∧ δ ≤ (1 + x) / 2)
    (r : ℕ) :
    |seedEll α β r x| ≤ 3 * ((α + β + 1 : ℕ) : ℝ) / 4 * seedQ α β δ ^ r := by
  set P : ℕ := α + β + 1 with hP
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp only [seedEll_zero, abs_zero, pow_zero, mul_one]; positivity
  have hδ1 : δ ≤ 1 := by linarith [hx.1, hx.2]
  have b1 := abs_centeredPowerSum_div_le (p := P) (P := P) le_rfl hδ hδ1 r
  have b2 := abs_centeredPowerSum_div_le (p := α) (P := P) (by omega) hδ hx.1 r
  have b3 := abs_centeredPowerSum_div_le (p := β) (P := P) (by omega) hδ hx.2 r
  rw [one_pow, div_one] at b1
  have hq : ((P : ℝ) / (2 * δ)) ^ (2 * r) = seedQ α β δ ^ r := by rw [seedQ, pow_mul]
  rw [hq] at b1 b2 b3
  unfold seedEll
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (4 * (r : ℝ)))]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hbr : |centeredPowerSum P (2 * r) - centeredPowerSum α (2 * r) / ((1 - x) / 2) ^ (2 * r) -
      centeredPowerSum β (2 * r) / ((1 + x) / 2) ^ (2 * r)| ≤ 3 * P * seedQ α β δ ^ r := by
    calc _ ≤ |centeredPowerSum P (2 * r) - centeredPowerSum α (2 * r) / ((1 - x) / 2) ^ (2 * r)| +
          |centeredPowerSum β (2 * r) / ((1 + x) / 2) ^ (2 * r)| := abs_sub _ _
      _ ≤ (|centeredPowerSum P (2 * r)| +
            |centeredPowerSum α (2 * r) / ((1 - x) / 2) ^ (2 * r)|) +
          |centeredPowerSum β (2 * r) / ((1 + x) / 2) ^ (2 * r)| := by
          gcongr; exact abs_sub _ _
      _ ≤ 3 * P * seedQ α β δ ^ r := by linarith
  have hqr : 0 ≤ seedQ α β δ ^ r := by unfold seedQ; positivity
  calc 1 / (4 * (r : ℝ)) * _ ≤ 1 / 4 * (3 * P * seedQ α β δ ^ r) := by
        refine mul_le_mul ?_ hbr (abs_nonneg _) (by norm_num)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    _ = _ := by ring

theorem seedOK_of_uniform (α β : ℕ) {δ : ℝ} (hδ : 0 < δ) {x t : ℝ}
    (hx : δ ≤ (1 - x) / 2 ∧ δ ≤ (1 + x) / 2) (ht : 0 ≤ t) (hqt : seedQ α β δ * t ≤ 1 / 2) :
    SeedOK α β x t := by
  have hδ1 : δ ≤ 1 / 2 := by linarith [hx.1, hx.2]
  have hPt : ((α + β + 1 : ℕ) : ℝ) ^ 2 * t ≤ 2 * δ ^ 2 := by
    have : ((α + β + 1 : ℕ) : ℝ) ^ 2 * t = seedQ α β δ * t * (4 * δ ^ 2) := by
      unfold seedQ; field_simp; ring
    rw [this]; nlinarith [sq_nonneg δ]
  have hα : (α : ℝ) ^ 2 ≤ ((α + β + 1 : ℕ) : ℝ) ^ 2 := by
    gcongr; linarith [Nat.cast_nonneg (α := ℝ) β]
  have hβ : (β : ℝ) ^ 2 ≤ ((α + β + 1 : ℕ) : ℝ) ^ 2 := by
    gcongr; linarith [Nat.cast_nonneg (α := ℝ) α]
  refine ⟨by linarith [hx.1], by linarith [hx.2], ht, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_right hα ht, pow_le_pow_left₀ hδ.le hx.1 2]
  · nlinarith [mul_le_mul_of_nonneg_right hβ ht, pow_le_pow_left₀ hδ.le hx.2 2]
  · nlinarith

theorem eventually_seedQ (q : ℝ) :
    ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 ≤ t ∧ q * t ≤ 1 / 2 := by
  refine (eventually_nhdsWithin_of_forall fun t ht => ht).and ?_
  have : ∀ᶠ t in 𝓝 (0 : ℝ), q * t < 1 / 2 :=
    (continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simp)
  exact nhdsWithin_le_nhds (this.mono fun t ht => ht.le)

/-- **`eq:3jseedlogallorder` as a uniform asymptotic expansion.**  `log seedRatio α β x t`
has the expansion `∑_r ℓ_r(x) t^r` as `t → 0⁺`, uniformly for `x` with `u_± ≥ δ > 0`. -/
theorem seedRatio_log_hasUniformExpansion (α β : ℕ) {δ : ℝ} (hδ : 0 < δ) {K : Set ℝ}
    (hK : ∀ x ∈ K, δ ≤ (1 - x) / 2 ∧ δ ≤ (1 + x) / 2) :
    HasUniformExpansion (fun x t => Real.log (seedRatio α β x t)) (seedEll α β)
      (fun t : ℝ => t) (𝓝[≥] 0) K := by
  refine hasUniformExpansion_of_hasSum_geom (C := 3 * ((α + β + 1 : ℕ) : ℝ) / 4)
    (q := seedQ α β δ) (by unfold seedQ; positivity)
    (fun x hx r => abs_seedEll_le α β hδ (hK x hx) r) (eventually_seedQ _) ?_
  intro x hx t ht hqt
  have := seedRatio_log_hasSum (seedOK_of_uniform α β hδ (hK x hx) ht hqt)
  simpa [mul_comm] using this

/-- **The seed ratio itself.**  `seedRatio α β x t` has the uniform expansion `∑_r κ_r(x) t^r`
with `κ_r(x) = [t^r] exp(∑_{s≥1} ℓ_s(x) t^s)` (`expCoeff`). -/
theorem seedRatio_hasUniformExpansion (α β : ℕ) {δ : ℝ} (hδ : 0 < δ) {K : Set ℝ}
    (hK : ∀ x ∈ K, δ ≤ (1 - x) / 2 ∧ δ ≤ (1 + x) / 2) :
    HasUniformExpansion (seedRatio α β) (expCoeff (seedEll α β)) (fun t : ℝ => t)
      (𝓝[≥] 0) K := by
  have h := (seedRatio_log_hasUniformExpansion α β hδ hK).exp (fun x => seedEll_zero α β x)
    (tendsto_id.mono_left nhdsWithin_le_nhds)
  refine HasExpansionAlong.congr_left h ?_
  rw [eventually_principal_prod_iff]
  filter_upwards [eventually_seedQ (seedQ α β δ)] with t ht x hx
  exact Real.exp_log (seedOK_of_uniform α β hδ (hK x hx) ht.1 ht.2).pos

/-- A compact `K ⊆ (-1,1)` is uniformly inside `{u_± ≥ δ}` for some `δ > 0`. -/
theorem exists_delta_of_compact {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Set.Ioo (-1 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ (1 - x) / 2 ∧ δ ≤ (1 + x) / 2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne
    (f := fun x : ℝ => min ((1 - x) / 2) ((1 + x) / 2)) (by fun_prop)
  refine ⟨min ((1 - x0) / 2) ((1 + x0) / 2), ?_, fun x hx => ?_⟩
  · have := hKI hx0
    exact lt_min (by linarith [this.2]) (by linarith [this.1])
  · have : min ((1 - x0) / 2) ((1 + x0) / 2) ≤ min ((1 - x) / 2) ((1 + x) / 2) := hmin hx
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩

theorem seedRatio_log_hasUniformExpansion_compact (α β : ℕ) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Set.Ioo (-1 : ℝ) 1) :
    HasUniformExpansion (fun x t => Real.log (seedRatio α β x t)) (seedEll α β)
      (fun t : ℝ => t) (𝓝[≥] 0) K := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_compact hK hKI
  exact seedRatio_log_hasUniformExpansion α β hδ h

theorem seedRatio_hasUniformExpansion_compact (α β : ℕ) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Set.Ioo (-1 : ℝ) 1) :
    HasUniformExpansion (seedRatio α β) (expCoeff (seedEll α β)) (fun t : ℝ => t)
      (𝓝[≥] 0) K := by
  obtain ⟨δ, hδ, h⟩ := exists_delta_of_compact hK hKI
  exact seedRatio_hasUniformExpansion α β hδ h

/-- info: 'FormalResearch.Racah.seedRatio_log_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedRatio_log_hasSum

/-- info: 'FormalResearch.Racah.seedRatio_log_hasUniformExpansion_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedRatio_log_hasUniformExpansion_compact

/-- info: 'FormalResearch.Racah.seedRatio_hasUniformExpansion_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedRatio_hasUniformExpansion_compact

/-- info: 'FormalResearch.Racah.seedRatio_log_hasUniformExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedRatio_log_hasUniformExpansion

/-- info: 'FormalResearch.Racah.seedRatio_hasUniformExpansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedRatio_hasUniformExpansion

end FormalResearch.Racah
