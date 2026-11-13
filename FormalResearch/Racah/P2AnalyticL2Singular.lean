module

public import FormalResearch.Racah.P2HahnBeta
public import FormalResearch.Racah.P2HahnKernel
public import FormalResearch.Special.JacobiCD
public import FormalResearch.Special.JacobiOrth

/-!
# The singular-pair relation of the beta-binomial channel in `L²(ν_H)` (Weyl P2)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `prop:betabinomialpolar`
(`eq:singularvaluesgeneral`, `eq:betameasure`-`eq:conditionalC`) and Appendix `app:beta-polar`
(`eq:BernsteinAdjoint`, `eq:BernsteinHahnJacobi`).

Notation (`α β D n : ℕ`, `n ≤ D`): `ν_H = t^α(1-t)^β/B dt` on `[0,1]` (`wtJ`, `betaB`, `ipJ`),
`p_D` (`pD`, `eq:betabinomialmass`), `C_D` (`CopBeta`, `eq:conditionalC`), `C_D^*` (`Cstar`,
`eq:BernsteinAdjoint`), Jacobi mode `jT` (`= n!/(α+1)_n P_n^{(α,β)}(1-2t)`), Hahn polynomial `hahnQ`.

## Proved here

* `beta01`: `∫_0^1 t^a(1-t)^b dt = a!b!/(a+b+1)!`; `pD_eq_integral`, `pD_eq_hahnW`: the beta formula for
  `p_D` equals `(1/B)∫ b_u^D dν` and `w_H(u)/∑w_H`;
* `ipJ_jT_orth`, `ipJ_jT_pos`: Jacobi orthogonality in `L²(ν_H)` (from `jacobi_orthogonal`);
* `hahn_orth`, `hahn_determined`: Hahn orthogonality in `ℓ²(p_D)` (from `Phi_discorth` via `Phi3j_hahn`)
  and completeness of `{Q_m}_{m≤D}` (dimension count);
* `ipP_Cop`: adjointness of `C_D` and `C_D^*`;
* `Cop_jT`: `C_D jT_n = s_n² Q_n` on `{0..D}`; `norm_relation`: `‖jT_n‖²_ν = s_n² ‖Q_n‖²_p`;
* `singular_pair`: `T_D J_n = s_n H_n` (`eq:singularvaluesgeneral`), `s_n² = singularSq`
  (`= D^{\underline n}/(D+α+β+2)_n`, positive for `n ≤ D`, `singularSq_pos`), which with
  `singularSq_physical` is `eq:physicalsingularvalues`.

The polar factor `U_D`, the gauges `G_c`, `G_d`, `eq:SNpolar` and the whitening formula are in `P2AnalyticL2PolarAbs`, `P2AnalyticL2Polar`, `Polar2`, `Polar3`, `Polar4`.
-/

@[expose] public section

namespace FormalResearch.Racah

open Polynomial FormalResearch.Special FormalResearch.Wigner MeasureTheory

/-! ### Beta integrals on `[0,1]` and the Jacobi weight in `t = (1-x)/2` -/

/-- `∫_0^1 F(t) dt = ½ ∫_{-1}^1 F((1-x)/2) dx`. -/
lemma integral01_eq (F : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, F t = (1 / 2) * ∫ x in (-1 : ℝ)..1, F ((1 - x) / 2) := by
  have h := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1) (c := 2)
    (fun x => F ((1 - x) / 2)) (by norm_num) 1
  have e : ∀ t : ℝ, F ((1 - (1 - 2 * t)) / 2) = F t := fun t => by congr 1; ring
  simp only [e] at h
  rw [h]
  norm_num

/-- The beta integral on `[0,1]` for natural parameters. -/
theorem beta01 (a b : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ a * (1 - t) ^ b =
      (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  rw [integral01_eq]
  have e : ∀ x : ℝ, ((1 - x) / 2) ^ a * (1 - (1 - x) / 2) ^ b =
      (1 / 2) ^ (a + b) * ((1 - x) ^ a * (1 + x) ^ b) := fun x => by
    rw [show (1 - (1 - x) / 2) = (1 + x) / 2 by ring, div_pow, div_pow, pow_add, one_div, inv_pow,
      inv_pow]
    ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, beta_nat]
  have hf : ((a + b + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [one_div, inv_pow, pow_succ]
  field_simp

/-! ### The Jacobi side -/

/-- The terminating `₂F₁(-n, n+α+β+1; α+1; t)` (`= n!/(α+1)_n · P_n^{(α,β)}(1-2t)`), the right
side of `eq:BernsteinHahnJacobi`. -/
noncomputable def jT (α β n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
      ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (k.factorial : ℝ)) * t ^ k

/-- The constant `n!/(α+1)_n` relating `jT` to `P_n^{(α,β)}(1-2t)`. -/
noncomputable def cJ (α n : ℕ) : ℝ := (n.factorial : ℝ) / (ascPochhammer ℝ n).eval ((α : ℝ) + 1)

lemma jT_eq_jacobi (α β n : ℕ) (t : ℝ) :
    jT α β n t = cJ α n * (jacobi (α : ℝ) (β : ℝ) n).eval (1 - 2 * t) :=
  hypergeometric_eq_jacobi α β n t

lemma jT_continuous (α β n : ℕ) : Continuous (jT α β n) := by
  unfold jT
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)

lemma cJ_pos (α n : ℕ) : 0 < cJ α n := by
  unfold cJ
  exact div_pos (by positivity) (ascPochhammer_pos n _ (by positivity))

/-- The Jacobi weight `t^α (1-t)^β` on `[0,1]`. -/
noncomputable def wtJ (α β : ℕ) (t : ℝ) : ℝ := t ^ α * (1 - t) ^ β

lemma wtJ_continuous (α β : ℕ) : Continuous (wtJ α β) := by
  unfold wtJ; fun_prop

/-- The weighted inner product `∫_0^1 t^α(1-t)^β f g dt` (`L²(ν_H)` up to the factor `B`). -/
noncomputable def ipJ (α β : ℕ) (f g : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, wtJ α β t * (f t * g t)

lemma wtJ_half (α β : ℕ) (x : ℝ) :
    wtJ α β ((1 - x) / 2) = (1 / 2) ^ (α + β) * ((1 - x) ^ α * (1 + x) ^ β) := by
  unfold wtJ
  rw [show (1 - (1 - x) / 2) = (1 + x) / 2 by ring, div_pow, div_pow, pow_add, one_div, inv_pow,
    inv_pow]
  ring

lemma jT_half (α β n : ℕ) (x : ℝ) :
    jT α β n ((1 - x) / 2) = cJ α n * (jacobi (α : ℝ) (β : ℝ) n).eval x := by
  rw [jT_eq_jacobi]; congr 2; ring

/-- **Orthogonality of the Jacobi modes in `L²(ν_H)`**: `∫_0^1 t^α(1-t)^β jT_n jT_m dt = 0`,
`n ≠ m`. -/
theorem ipJ_jT_orth (α β : ℕ) {n m : ℕ} (h : n ≠ m) : ipJ α β (jT α β n) (jT α β m) = 0 := by
  unfold ipJ
  rw [integral01_eq]
  have e : ∀ x : ℝ, wtJ α β ((1 - x) / 2) * (jT α β n ((1 - x) / 2) * jT α β m ((1 - x) / 2)) =
      ((1 / 2) ^ (α + β) * cJ α n * cJ α m) * ((1 - x) ^ α * (1 + x) ^ β *
        (jacobi (α : ℝ) (β : ℝ) n).eval x * (jacobi (α : ℝ) (β : ℝ) m).eval x) := by
    intro x
    rw [wtJ_half, jT_half, jT_half]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, jacobi_orthogonal α β n m h]
  simp

/-- The squared norm of `jT_n` in `L²(ν_H)` (up to `B`): it is positive. -/
theorem ipJ_jT_pos (α β n : ℕ) : 0 < ipJ α β (jT α β n) (jT α β n) := by
  unfold ipJ
  rw [integral01_eq]
  have e : ∀ x : ℝ, wtJ α β ((1 - x) / 2) * (jT α β n ((1 - x) / 2) * jT α β n ((1 - x) / 2)) =
      ((1 / 2) ^ (α + β) * cJ α n ^ 2) * ((1 - x) ^ α * (1 + x) ^ β *
        ((jacobi (α : ℝ) (β : ℝ) n).eval x) ^ 2) := by
    intro x
    rw [wtJ_half, jT_half]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, jacobi_norm]
  have := cJ_pos α n
  positivity

/-! ### The beta-binomial side -/

/-- `B(a+1, b+1) = a! b!/(a+b+1)!`. -/
noncomputable def betaB (a b : ℕ) : ℝ :=
  (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ)

lemma betaB_pos (a b : ℕ) : 0 < betaB a b := by unfold betaB; positivity

/-- The beta-binomial mass function `p_D(u) = C(D,u) B(u+α+1, D-u+β+1)/B(α+1, β+1)`
(`eq:betabinomialmass`). -/
noncomputable def pD (α β D u : ℕ) : ℝ :=
  (D.choose u : ℝ) * betaB (u + α) (D - u + β) / betaB α β

lemma pD_pos (α β D u : ℕ) (hu : u ≤ D) : 0 < pD α β D u := by
  unfold pD
  have : (0 : ℝ) < (D.choose u : ℝ) := by exact_mod_cast Nat.choose_pos hu
  have := betaB_pos (u + α) (D - u + β)
  have := betaB_pos α β
  positivity

/-- `p_D(u) = (1/B) ∫_0^1 b_u^D(t) t^α (1-t)^β dt`: the marginal of the beta-binomial law. -/
theorem pD_eq_integral (α β D u : ℕ) :
    pD α β D u = (1 / betaB α β) * ∫ t in (0 : ℝ)..1, bern D u t * wtJ α β t := by
  have e : ∀ t : ℝ, bern D u t * wtJ α β t =
      (D.choose u : ℝ) * (t ^ (u + α) * (1 - t) ^ (D - u + β)) := by
    intro t; unfold bern wtJ; rw [pow_add, pow_add]; ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul, beta01]
  unfold pD betaB
  have h1 : (α.factorial : ℝ) * β.factorial / (α + β + 1).factorial ≠ 0 := by positivity
  field_simp

/-- The beta-binomial inner product `⟨f, g⟩_{p_D} = ∑_u p_D(u) f(u) g(u)` on `{0,…,D}`. -/
noncomputable def ipP (α β D : ℕ) (f g : ℕ → ℝ) : ℝ :=
  ∑ u ∈ Finset.range (D + 1), pD α β D u * (f u * g u)

/-- The conditional expectation `(C_D f)(u) = p_D(u)⁻¹ ∫_0^1 b_u^D f dν_H` (`eq:conditionalC`),
`dν_H = t^α (1-t)^β/B dt`. -/
noncomputable def CopBeta (α β D : ℕ) (f : ℝ → ℝ) (u : ℕ) : ℝ :=
  (1 / pD α β D u) * ((1 / betaB α β) * ∫ t in (0 : ℝ)..1, bern D u t * f t * wtJ α β t)

/-- The Bernstein averaging operator `(C_D^* g)(t) = ∑_u b_u^D(t) g(u)` (`eq:BernsteinAdjoint`). -/
noncomputable def Cstar (D : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (D + 1), bern D u t * g u

lemma bern_continuous (D u : ℕ) : Continuous (bern D u) := by
  unfold bern; fun_prop

/-- **Adjointness**: `⟨C_D f, g⟩_{p_D} = (1/B) ∫ f (C_D^* g) t^α(1-t)^β dt = ⟨f, C_D^* g⟩_{ν_H}`. -/
theorem ipP_Cop (α β D : ℕ) {f : ℝ → ℝ} (hf : Continuous f) (g : ℕ → ℝ) :
    ipP α β D (CopBeta α β D f) g =
      (1 / betaB α β) * ∫ t in (0 : ℝ)..1, wtJ α β t * (f t * Cstar D g t) := by
  unfold ipP
  have h1 : ∀ u ∈ Finset.range (D + 1), pD α β D u * (CopBeta α β D f u * g u) =
      (1 / betaB α β) * ∫ t in (0 : ℝ)..1, wtJ α β t * (f t * (bern D u t * g u)) := by
    intro u hu
    have hp := (pD_pos α β D u (by simpa [Nat.lt_succ_iff] using hu)).ne'
    unfold CopBeta
    have e : ∀ t : ℝ, wtJ α β t * (f t * (bern D u t * g u)) =
        g u * (bern D u t * f t * wtJ α β t) := fun t => by ring
    simp only [e]
    rw [intervalIntegral.integral_const_mul]
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  congr 1
  have hint : ∀ u ∈ Finset.range (D + 1), IntervalIntegrable
      (fun t => wtJ α β t * (f t * (bern D u t * g u))) MeasureTheory.volume 0 1 := by
    intro u _
    exact ((wtJ_continuous α β).mul (hf.mul ((bern_continuous D u).mul continuous_const))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Cstar, Finset.mul_sum]

/-! ### The Hahn side: `p_D = w_H / ∑ w_H`, orthogonality and completeness -/

lemma pD_eq_hahnW (α β D u : ℕ) (hu : u ≤ D) :
    pD α β D u = (hahnW α β D u : ℝ) / ((α + β + 1 + D).choose D : ℝ) := by
  unfold pD betaB hahnW
  have e1 : (u + α + (D - u + β) + 1) = α + β + 1 + D := by omega
  rw [e1]
  have c1 : (((α + u).choose u : ℕ) : ℝ) =
      ((α + u).factorial : ℝ) / ((u.factorial : ℝ) * (α.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : u ≤ α + u)]
    simp
  have c2 : (((β + (D - u)).choose (D - u) : ℕ) : ℝ) =
      ((β + (D - u)).factorial : ℝ) / (((D - u).factorial : ℝ) * (β.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : D - u ≤ β + (D - u))]
    simp
  have c3 : ((D.choose u : ℕ) : ℝ) = (D.factorial : ℝ) / ((u.factorial : ℝ) * ((D - u).factorial : ℝ)) :=
    Nat.cast_choose ℝ hu
  have c4 : (((α + β + 1 + D).choose D : ℕ) : ℝ) =
      ((α + β + 1 + D).factorial : ℝ) / ((D.factorial : ℝ) * ((α + β + 1).factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (by omega : D ≤ α + β + 1 + D)]
    simp
  rw [Nat.cast_mul, c1, c2, c3, c4, show β + (D - u) = D - u + β by ring,
    show α + u = u + α by ring]
  have : ((u + α).factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma ipP_one (α β D : ℕ) : ipP α β D (fun _ => 1) (fun _ => 1) = 1 := by
  unfold ipP
  have h : ∀ u ∈ Finset.range (D + 1), pD α β D u * ((1 : ℝ) * 1) =
      (hahnW α β D u : ℝ) / ((α + β + 1 + D).choose D : ℝ) := by
    intro u hu'
    rw [mul_one, mul_one]
    exact pD_eq_hahnW α β D u (by simpa [Nat.lt_succ_iff] using hu')
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, ← Nat.cast_sum, hahnW_sum]
  have : (0 : ℝ) < ((α + β + 1 + D).choose (α + β + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  rw [show (α + β + 1 + D).choose D = (α + β + 1 + D).choose (α + β + 1) by
    rw [Nat.choose_symm_of_eq_add]; ring]
  field_simp

lemma hahnQ_at_zero (α β D n : ℕ) : hahnQ α β D n 0 = 1 := by
  unfold hahnQ
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have : (ascPochhammer ℝ (j + 1)).eval (-((0 : ℕ) : ℝ)) = 0 := by
      rw [ascPochhammer_succ_left]; simp
    rw [this]; simp
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

lemma hahnNorm_pos (α β D n : ℕ) : 0 < hahnNorm α β D n := by
  unfold hahnNorm
  have h0 : (0 : ℝ) < hahnW α β D 0 := by
    unfold hahnW
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  calc (0 : ℝ) < (hahnW α β D 0 : ℝ) * hahnQ α β D n 0 ^ 2 := by
        rw [hahnQ_at_zero]; simpa using h0
    _ ≤ _ := Finset.single_le_sum (f := fun u => (hahnW α β D u : ℝ) * hahnQ α β D n u ^ 2)
        (fun u _ => by positivity) (Finset.mem_range.2 (by omega))

/-- **Orthogonality of the Hahn polynomials** `Q_n(·;α,β,D)` for the weight `w_H`, `n ≠ m ≤ D`,
obtained from the exact discrete orthogonality `Phi_discorth` of the `3j` kernel via
`Phi3j_hahn` (physical chamber `M = (α+β)/2`, `σ = (β-α)/2`, `N = D+M+1`). -/
theorem hahn_orth (α β D n m : ℕ) (hn : n ≤ D) (hm : m ≤ D) (hnm : n ≠ m) :
    ∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) *
      (hahnQ α β D n u * hahnQ α β D m u) = 0 := by
  set M : ℚ := ((α : ℚ) + β) / 2 with hM
  set σ : ℚ := ((β : ℚ) - α) / 2 with hσ
  set N : ℚ := D + M + 1 with hN
  have hα : M - σ = α := by rw [hM, hσ]; ring
  have hβ : M + σ = β := by rw [hM, hσ]; ring
  have hD : N - M - 1 = D := by rw [hN]; ring
  obtain ⟨hMr, hsr, hNr⟩ := chamber_real hα hβ hD
  have hNp : (0 : ℝ) < N := by rw [hNr]; positivity
  have hNq : 0 < N := by exact_mod_cast hNp
  have hA := chamber_specAdm hα hβ hD
  have hK : ((D + 1 : ℕ) : ℚ) = N - max |M| |σ| := by
    rw [chamber_max hα hβ]; push_cast; linarith
  have hT : ∀ k : ℕ, k ≤ D → IsTri (M + k) (jMinus N σ) (jPlus N σ) := by
    intro k hk
    refine ⟨⟨α + k, ?_⟩, ⟨β + k, ?_⟩, ⟨D - k, ?_⟩⟩
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; push_cast; linarith
    · unfold jMinus jPlus; rw [Nat.cast_sub hk]; linarith
  have h1 : ∀ k : ℕ, IsNat (M + k + M) := fun k => ⟨α + β + k, by push_cast; linarith⟩
  have h2 : ∀ k : ℕ, IsNat (M + k - M) := fun k => ⟨k, by ring⟩
  have hdo := Phi_discorth hA hNq hK (hT n hn) (h1 n) (h2 n) (hT m hm) (h1 m) (h2 m)
  have hne : ¬ (M + n = M + m) := fun e => hnm (by exact_mod_cast (by linarith : (n : ℚ) = m))
  rw [ite_eq_right hne] at hdo
  set hn_ := hahnNorm α β D n with hhn
  set hm_ := hahnNorm α β D m with hhm
  have hhnp : 0 < hn_ := hahnNorm_pos α β D n
  have hhmp : 0 < hm_ := hahnNorm_pos α β D m
  set A : ℝ := Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + n) + 1)) *
    Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + m) + 1)) / (Real.sqrt hn_ * Real.sqrt hm_) with hAdef
  have hMnn : (0 : ℝ) ≤ M := by rw [hMr]; positivity
  have hApos : 0 < A := by
    rw [hAdef]
    have : (0 : ℝ) < 2 * ((M : ℝ) + n) + 1 := by positivity
    have : (0 : ℝ) < 2 * ((M : ℝ) + m) + 1 := by positivity
    positivity
  have hterm : ∀ n' ∈ Finset.range (D + 1),
      PhiX (M + n) M σ N (xLat M σ N n') * PhiX (M + m) M σ N (xLat M σ N n') =
        A * ((hahnW α β D (D - n') : ℝ) *
          (hahnQ α β D n (D - n') * hahnQ α β D m (D - n'))) := by
    intro n' hn'
    have hn'D : n' ≤ D := by simp only [Finset.mem_range] at hn'; omega
    have hx : ∀ k : ℕ, PhiX (M + k) M σ N (xLat M σ N n') =
        Phi3j (M + k) M σ N ((-N + 1 + |M + σ|) / 2 + n') := by
      intro k; unfold PhiX; rw [mu_lat M σ N hNq.ne']
    rw [hx, hx, Phi3j_hahn hα hβ hD n (D - n') hn (lat_u hα hβ hD n' hn'D) (by omega),
      Phi3j_hahn hα hβ hD m (D - n') hm (lat_u hα hβ hD n' hn'D) (by omega)]
    have hw : (0 : ℝ) ≤ hahnW α β D (D - n') := by positivity
    rw [Real.sqrt_div hw, Real.sqrt_div hw]
    have hsq : (Real.sqrt (hahnW α β D (D - n') : ℝ)) ^ 2 = hahnW α β D (D - n') :=
      Real.sq_sqrt hw
    have hs1 : (-1 : ℝ) ^ α * (-1 : ℝ) ^ α = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    have hsn : Real.sqrt hn_ ≠ 0 := (Real.sqrt_pos.2 hhnp).ne'
    have hsm : Real.sqrt hm_ ≠ 0 := (Real.sqrt_pos.2 hhmp).ne'
    rw [hAdef]
    generalize Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + n) + 1)) = P
    generalize Real.sqrt ((N : ℝ) / (2 * ((M : ℝ) + m) + 1)) = R
    generalize Real.sqrt (hahnW α β D (D - n') : ℝ) = ω at hsq ⊢
    generalize Real.sqrt hn_ = s1
    generalize Real.sqrt hm_ = s2
    generalize hahnQ α β D n (D - n') = Qn
    generalize hahnQ α β D m (D - n') = Qm
    have e : ((-1 : ℝ) ^ α * P * (ω / s1) * Qn) * ((-1 : ℝ) ^ α * R * (ω / s2) * Qm) =
        ((-1 : ℝ) ^ α * (-1 : ℝ) ^ α) * (ω * ω) * (P * R / (s1 * s2)) * (Qn * Qm) := by ring
    rw [e, hs1, ← sq, hsq]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at hdo
  have hrefl : ∑ n' ∈ Finset.range (D + 1), (hahnW α β D (D - n') : ℝ) *
      (hahnQ α β D n (D - n') * hahnQ α β D m (D - n')) =
      ∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) * (hahnQ α β D n u * hahnQ α β D m u) :=
    Finset.sum_range_reflect (fun u => (hahnW α β D u : ℝ) *
      (hahnQ α β D n u * hahnQ α β D m u)) (D + 1)
  rw [hrefl] at hdo
  have hNr' : (N : ℝ) ≠ 0 := hNp.ne'
  have : 2 * (1 / (N : ℝ)) * A ≠ 0 := by positivity
  rcases mul_eq_zero.1 (show (2 * (1 / (N : ℝ)) * A) * ∑ u ∈ Finset.range (D + 1),
      (hahnW α β D u : ℝ) * (hahnQ α β D n u * hahnQ α β D m u) = 0 by linarith) with h | h
  · exact absurd h this
  · exact h

/-- The weighted vector `i ↦ √p_D(i) f(i)` of `ℝ^{D+1}`. -/
noncomputable def wvec (α β D : ℕ) (f : ℕ → ℝ) : EuclideanSpace ℝ (Fin (D + 1)) :=
  WithLp.toLp 2 (fun i : Fin (D + 1) => Real.sqrt (pD α β D i) * f i)

lemma inner_wvec (α β D : ℕ) (f g : ℕ → ℝ) :
    inner ℝ (wvec α β D f) (wvec α β D g) = ipP α β D f g := by
  unfold wvec ipP
  rw [PiLp.inner_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun u => pD α β D u * (f u * g u)) (D + 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp : 0 ≤ pD α β D i := (pD_pos α β D i (by omega)).le
  have := Real.mul_self_sqrt hp
  simp only [RCLike.inner_apply, conj_trivial]
  linear_combination (f i * g i) * this

/-- **Completeness of the Hahn polynomials** in `ℓ²(p_D)`: a function on `{0,…,D}` orthogonal to
all `Q_m`, `m ≤ D`, vanishes. -/
theorem hahn_determined (α β D : ℕ) (g : ℕ → ℝ)
    (h : ∀ m ≤ D, ipP α β D g (hahnQ α β D m) = 0) : ∀ u ≤ D, g u = 0 := by
  classical
  let v : Fin (D + 1) → EuclideanSpace ℝ (Fin (D + 1)) := fun m => wvec α β D (hahnQ α β D m)
  have hnorm : ∀ m : Fin (D + 1), ipP α β D (hahnQ α β D m) (hahnQ α β D m) ≠ 0 := by
    intro m
    have hpd : ∀ u ∈ Finset.range (D + 1), pD α β D u * (hahnQ α β D m u * hahnQ α β D m u) =
        ((hahnW α β D u : ℝ) * hahnQ α β D m u ^ 2) / ((α + β + 1 + D).choose D : ℝ) := by
      intro u hu
      rw [pD_eq_hahnW α β D u (by simpa [Nat.lt_succ_iff] using hu)]; ring
    unfold ipP
    rw [Finset.sum_congr rfl hpd, ← Finset.sum_div]
    have : (0 : ℝ) < ((α + β + 1 + D).choose D : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    have h2 := hahnNorm_pos α β D m
    unfold hahnNorm at h2
    positivity
  have hli : LinearIndependent ℝ v := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun m hm => ?_) (fun m m' hmm => ?_)
    · apply hnorm m
      rw [← inner_wvec]
      change inner ℝ (v m) (v m) = 0
      rw [hm]; simp
    · change inner ℝ (wvec α β D (hahnQ α β D m)) (wvec α β D (hahnQ α β D m')) = 0
      rw [inner_wvec]
      unfold ipP
      have hpd : ∀ u ∈ Finset.range (D + 1), pD α β D u *
          (hahnQ α β D m u * hahnQ α β D m' u) =
          ((hahnW α β D u : ℝ) * (hahnQ α β D m u * hahnQ α β D m' u)) /
            ((α + β + 1 + D).choose D : ℝ) := by
        intro u hu
        rw [pD_eq_hahnW α β D u (by simpa [Nat.lt_succ_iff] using hu)]; ring
      rw [Finset.sum_congr rfl hpd, ← Finset.sum_div,
        hahn_orth α β D m m' (by omega) (by omega) (fun e => hmm (Fin.ext e))]
      simp
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  set G := wvec α β D g with hG
  have hz : inner ℝ G G = 0 := by
    have hall : ∀ x ∈ Submodule.span ℝ (Set.range v), inner ℝ G x = 0 := by
      intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨m, rfl⟩
        change inner ℝ (wvec α β D g) (wvec α β D (hahnQ α β D m)) = 0
        rw [inner_wvec]; exact h m (by omega)
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy]; simp
      · intro a x _ hx; rw [inner_smul_right, hx]; simp
    exact hall G (by rw [hspan]; trivial)
  have hG0 : G = 0 := inner_self_eq_zero.1 hz
  intro u hu
  have := congrArg (fun x : EuclideanSpace ℝ (Fin (D + 1)) => x ⟨u, by omega⟩) hG0
  simp only [hG, wvec, PiLp.zero_apply, WithLp.ofLp_toLp] at this
  have hp := (pD_pos α β D u hu).ne'
  have hsp : Real.sqrt (pD α β D u) ≠ 0 := (Real.sqrt_pos.2 (pD_pos α β D u hu)).ne'
  exact (mul_eq_zero.1 this).resolve_left hsp

/-! ### Chu--Vandermonde and the value at `u = 0` -/

lemma ascPoch_pos' (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 < (ascPochhammer ℝ k).eval c :=
  ascPochhammer_pos k c hc

/-- **Chu--Vandermonde**: `∑_{k≤n} (-1)^k C(n,k) (b)_k/(c)_k = (c-b)_n/(c)_n` for `c > 0`. -/
theorem chu_vandermonde (n : ℕ) : ∀ (b c : ℝ), 0 < c →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        ((ascPochhammer ℝ k).eval b / (ascPochhammer ℝ k).eval c) =
      (ascPochhammer ℝ n).eval (c - b) / (ascPochhammer ℝ n).eval c := by
  induction n with
  | zero => intro b c hc; simp
  | succ n ih =>
    intro b c hc
    have hc1 : 0 < c + 1 := by linarith
    -- Pascal split
    have hsplit : ∑ k ∈ Finset.range (n + 2), (-1 : ℝ) ^ k * ((n + 1).choose k : ℝ) *
          ((ascPochhammer ℝ k).eval b / (ascPochhammer ℝ k).eval c) =
        (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
          ((ascPochhammer ℝ k).eval b / (ascPochhammer ℝ k).eval c)) -
        (b / c) * ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
          ((ascPochhammer ℝ k).eval (b + 1) / (ascPochhammer ℝ k).eval (c + 1)) := by
      set T : ℕ → ℝ := fun k => (ascPochhammer ℝ k).eval b / (ascPochhammer ℝ k).eval c with hT
      have hTs : ∀ k, T (k + 1) = (b / c) * ((ascPochhammer ℝ k).eval (b + 1) /
          (ascPochhammer ℝ k).eval (c + 1)) := by
        intro k
        simp only [hT]
        have e1 := ascPoch_add_eval b 1 k
        have e2 := ascPoch_add_eval c 1 k
        rw [add_comm 1 k] at e1 e2
        rw [e1, e2]
        simp only [ascPochhammer_one, eval_X, Nat.cast_one]
        have hck : (ascPochhammer ℝ k).eval (c + 1) ≠ 0 := (ascPoch_pos' k hc1).ne'
        have hc0 : c ≠ 0 := hc.ne'
        field_simp
      rw [Finset.sum_range_succ' _ (n + 1)]
      have hpas : ∀ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) *
            T (k + 1) =
          (-(b / c)) * ((-1 : ℝ) ^ k * (n.choose k : ℝ) * ((ascPochhammer ℝ k).eval (b + 1) /
            (ascPochhammer ℝ k).eval (c + 1))) +
          ((-1 : ℝ) ^ (k + 1) * (n.choose (k + 1) : ℝ) * T (k + 1)) := by
        intro k _
        rw [Nat.choose_succ_succ, Nat.cast_add, hTs]
        ring
      rw [Finset.sum_congr rfl hpas, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hz : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ (k + 1) * (n.choose (k + 1) : ℝ) * T (k + 1)
          + (-1 : ℝ) ^ 0 * ((n + 1).choose 0 : ℝ) * T 0 =
          ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) * T k := by
        have h2 := Finset.sum_range_succ' (fun k => (-1 : ℝ) ^ k * (n.choose k : ℝ) * T k) (n + 1)
        have h3 := Finset.sum_range_succ (fun k => (-1 : ℝ) ^ k * (n.choose k : ℝ) * T k) (n + 1)
        simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
          Nat.choose_zero_right] at h2 h3 ⊢
        linarith
      linarith
    rw [hsplit, ih b c hc, ih (b + 1) (c + 1) hc1]
    have e3 : c + 1 - (b + 1) = c - b := by ring
    rw [e3]
    have e4 := ascPoch_add_eval c 1 n
    rw [add_comm 1 n] at e4
    have e5 : (ascPochhammer ℝ (n + 1)).eval c = (ascPochhammer ℝ n).eval c * (c + n) :=
      ascPochhammer_succ_eval n c
    have e6 : (ascPochhammer ℝ (n + 1)).eval (c - b) =
        (ascPochhammer ℝ n).eval (c - b) * (c - b + n) := ascPochhammer_succ_eval n (c - b)
    simp only [ascPochhammer_one, eval_X, Nat.cast_one] at e4
    rw [e6, e5]
    have hcn : (ascPochhammer ℝ n).eval c ≠ 0 := (ascPoch_pos' n hc).ne'
    have hcn1 : (ascPochhammer ℝ n).eval (c + 1) ≠ 0 := (ascPoch_pos' n hc1).ne'
    have hcn' : 0 < c + n := by positivity
    have hc0 : c ≠ 0 := hc.ne'
    have hk : (ascPochhammer ℝ n).eval (c + 1) = (ascPochhammer ℝ n).eval c * (c + n) / c := by
      field_simp
      linarith [e4, e5]
    rw [hk]
    field_simp
    ring

lemma ascPoch_fact (a k : ℕ) :
    (ascPochhammer ℝ k).eval ((a : ℝ) + 1) = ((a + k).factorial : ℝ) / (a.factorial : ℝ) := by
  have h := ascPoch_add_eval 1 a k
  rw [ascPoch_one_eval, ascPoch_one_eval, add_comm (1 : ℝ) a] at h
  have hf : (a.factorial : ℝ) ≠ 0 := by positivity
  rw [eq_div_iff hf, mul_comm]
  exact h.symm

/-- `(-n)_k / k! = (-1)^k C(n,k)`. -/
lemma poch_neg_div (n k : ℕ) :
    (ascPochhammer ℝ k).eval (-(n : ℝ)) / (k.factorial : ℝ) = (-1 : ℝ) ^ k * (n.choose k : ℝ) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The coefficient of `t^k` in `jT α β n`. -/
noncomputable def jcoef (α β n k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
    ((ascPochhammer ℝ k).eval ((α : ℝ) + 1) * (k.factorial : ℝ))

lemma jT_eq_sum (α β n : ℕ) (t : ℝ) :
    jT α β n t = ∑ k ∈ Finset.range (n + 1), jcoef α β n k * t ^ k := rfl

/-- The posterior moments at `u = 0`: `E[T^k | U = 0] = (α+1)_k/(D+α+β+2)_k`. -/
lemma Cop0_pow (α β D k : ℕ) :
    CopBeta α β D (fun t => t ^ k) 0 =
      (ascPochhammer ℝ k).eval ((α : ℝ) + 1) /
        (ascPochhammer ℝ k).eval ((D : ℝ) + α + β + 2) := by
  have hB := betaB_pos α β
  have hbern : ∀ t : ℝ, bern D 0 t = (1 - t) ^ D := fun t => by simp [bern]
  have hnum : ∫ t in (0 : ℝ)..1, bern D 0 t * t ^ k * wtJ α β t =
      (((α + k).factorial : ℝ) * ((D + β).factorial : ℝ)) / ((α + k + (D + β) + 1).factorial : ℝ) := by
    have e : ∀ t : ℝ, bern D 0 t * t ^ k * wtJ α β t = t ^ (α + k) * (1 - t) ^ (D + β) := by
      intro t; rw [hbern]; unfold wtJ; rw [pow_add, pow_add]; ring
    simp only [e]; exact beta01 _ _
  have hden : ∫ t in (0 : ℝ)..1, bern D 0 t * wtJ α β t =
      ((α.factorial : ℝ) * ((D + β).factorial : ℝ)) / ((α + (D + β) + 1).factorial : ℝ) := by
    have e : ∀ t : ℝ, bern D 0 t * wtJ α β t = t ^ α * (1 - t) ^ (D + β) := by
      intro t; rw [hbern]; unfold wtJ; rw [pow_add]; ring
    simp only [e]; exact beta01 _ _
  have hp0 := pD_eq_integral α β D 0
  unfold CopBeta
  rw [hnum]
  rw [hp0, hden]
  have h1 : ((α + k + (D + β) + 1).factorial : ℝ) =
      (((α + β + D + 1) + k).factorial : ℝ) := by
    rw [show α + k + (D + β) + 1 = α + β + D + 1 + k by omega]
  have h2 : ((α + (D + β) + 1).factorial : ℝ) = ((α + β + D + 1).factorial : ℝ) := by
    rw [show α + (D + β) + 1 = α + β + D + 1 by omega]
  rw [h1, h2]
  have hc : (D : ℝ) + α + β + 2 = ((α + β + D + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hc, ascPoch_fact, ascPoch_fact]
  have hf1 : ((α + k).factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((D + β).factorial : ℝ) ≠ 0 := by positivity
  have hf3 : (α.factorial : ℝ) ≠ 0 := by positivity
  have hf4 : ((α + β + D + 1).factorial : ℝ) ≠ 0 := by positivity
  have hf5 : ((α + β + D + 1 + k).factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma ipP_hahnQ_eq (α β D : ℕ) (f g : ℕ → ℝ) :
    ipP α β D f g = (∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) * (f u * g u)) /
      ((α + β + 1 + D).choose D : ℝ) := by
  unfold ipP
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [pD_eq_hahnW α β D u (by simpa [Nat.lt_succ_iff] using hu)]; ring

lemma ipP_Q_orth (α β D n m : ℕ) (hn : n ≤ D) (hm : m ≤ D) (hnm : n ≠ m) :
    ipP α β D (hahnQ α β D n) (hahnQ α β D m) = 0 := by
  rw [ipP_hahnQ_eq, hahn_orth α β D n m hn hm hnm]; simp

lemma ipP_Q_pos (α β D n : ℕ) : 0 < ipP α β D (hahnQ α β D n) (hahnQ α β D n) := by
  rw [ipP_hahnQ_eq]
  have : (0 : ℝ) < ((α + β + 1 + D).choose D : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have h2 := hahnNorm_pos α β D n
  unfold hahnNorm at h2
  have e : ∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) *
      (hahnQ α β D n u * hahnQ α β D n u) =
      ∑ u ∈ Finset.range (D + 1), (hahnW α β D u : ℝ) * hahnQ α β D n u ^ 2 :=
    Finset.sum_congr rfl fun u _ => by ring
  rw [e]
  positivity

/-- Linearity of `C_D` over finite combinations of continuous functions. -/
lemma Cop_sum (α β D : ℕ) (s : Finset ℕ) (c : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (hf : ∀ k, Continuous (f k))
    (u : ℕ) :
    CopBeta α β D (fun t => ∑ k ∈ s, c k * f k t) u = ∑ k ∈ s, c k * CopBeta α β D (f k) u := by
  unfold CopBeta
  have e : ∀ t : ℝ, bern D u t * (∑ k ∈ s, c k * f k t) * wtJ α β t =
      ∑ k ∈ s, c k * (bern D u t * f k t * wtJ α β t) := by
    intro t
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e]
  have hint : ∀ k ∈ s, IntervalIntegrable (fun t => c k * (bern D u t * f k t * wtJ α β t))
      MeasureTheory.volume 0 1 := fun k _ =>
    ((((bern_continuous D u).mul (hf k)).mul (wtJ_continuous α β)).const_mul (c k)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]; ring

lemma ascPoch_desc (n D : ℕ) :
    (ascPochhammer ℝ n).eval ((D : ℝ) + 1 - n) = (descPochhammer ℝ n).eval (D : ℝ) := by
  rw [descPochhammer_eval_eq_prod_range, ascPoch_eval_prod, ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun j hj => ?_
  have : j < n := Finset.mem_range.1 hj
  rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  ring

/-- The value at `u = 0`: `(C_D jT_n)(0) = s_n²` (Chu--Vandermonde). -/
theorem Cop0_jT (α β D n : ℕ) : CopBeta α β D (jT α β n) 0 = singularSq α β D n := by
  have h1 : CopBeta α β D (jT α β n) 0 = ∑ k ∈ Finset.range (n + 1), jcoef α β n k *
      CopBeta α β D (fun t => t ^ k) 0 :=
    Cop_sum α β D (Finset.range (n + 1)) (jcoef α β n) (fun k t => t ^ k)
      (fun k => continuous_pow k) 0
  have h1' : CopBeta α β D (jT α β n) 0 = _ := h1
  rw [h1']
  have hc : (0 : ℝ) < (D : ℝ) + α + β + 2 := by positivity
  have h2 : ∀ k ∈ Finset.range (n + 1), jcoef α β n k * CopBeta α β D (fun t => t ^ k) 0 =
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * ((ascPochhammer ℝ k).eval ((n : ℝ) + α + β + 1) /
        (ascPochhammer ℝ k).eval ((D : ℝ) + α + β + 2)) := by
    intro k _
    rw [Cop0_pow, ← poch_neg_div n k]
    unfold jcoef
    have hA : 0 < (ascPochhammer ℝ k).eval ((α : ℝ) + 1) := ascPoch_pos' k (by positivity)
    have hC := (ascPoch_pos' k hc).ne'
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl h2, chu_vandermonde n _ _ hc]
  unfold singularSq
  have : (D : ℝ) + α + β + 2 - ((n : ℝ) + α + β + 1) = (D : ℝ) + 1 - n := by ring
  rw [this, ascPoch_desc]

/-- `C_D^* Q_m = jT_m` (`eq:BernsteinHahnJacobi`) in the notation of this file. -/
lemma Cstar_hahnQ (α β D m : ℕ) (hm : m ≤ D) (t : ℝ) :
    Cstar D (hahnQ α β D m) t = jT α β m t :=
  bernstein_hahn_jacobi α β D m hm t

/-- **The singular-pair relation, unnormalised** (`eq:singularvaluesgeneral`): for `n ≤ D`,
`C_D jT_n = s_n² Q_n` on `{0,…,D}`, `s_n² = D^{\underline n}/(D+α+β+2)_n`; here `jT_n` is the
Jacobi mode (`= n!/(α+1)_n P_n^{(α,β)}(1-2t)`) and `Q_n` the Hahn polynomial.  The proof uses
adjointness, `C_D^* Q_m = jT_m`, orthogonality of `jT` in `L²(ν_H)` and of `Q` in `ℓ²(p_D)`,
completeness of `{Q_m}` in `ℓ²(p_D)` (`hahn_determined`), and the value at `u = 0`
(Chu--Vandermonde, `Cop0_jT`). -/
theorem Cop_jT (α β D n : ℕ) (hn : n ≤ D) {u : ℕ} (hu : u ≤ D) :
    CopBeta α β D (jT α β n) u = singularSq α β D n * hahnQ α β D n u := by
  have hB := betaB_pos α β
  set Gn := ipJ α β (jT α β n) (jT α β n) with hGn
  set Pn := ipP α β D (hahnQ α β D n) (hahnQ α β D n) with hPn
  have hPpos : 0 < Pn := ipP_Q_pos α β D n
  set κ := Gn / (betaB α β * Pn) with hκ
  have key : ∀ u ≤ D, CopBeta α β D (jT α β n) u = κ * hahnQ α β D n u := by
    have := hahn_determined α β D (fun u => CopBeta α β D (jT α β n) u - κ * hahnQ α β D n u) ?_
    · intro u hu; linarith [this u hu]
    intro m hm
    have hF : ipP α β D (CopBeta α β D (jT α β n)) (hahnQ α β D m) =
        (1 / betaB α β) * ipJ α β (jT α β n) (jT α β m) := by
      rw [ipP_Cop α β D (jT_continuous α β n)]
      unfold ipJ
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Cstar_hahnQ α β D m hm]
    have hlin : ipP α β D (fun u => CopBeta α β D (jT α β n) u - κ * hahnQ α β D n u)
        (hahnQ α β D m) = ipP α β D (CopBeta α β D (jT α β n)) (hahnQ α β D m) -
        κ * ipP α β D (hahnQ α β D n) (hahnQ α β D m) := by
      unfold ipP
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hlin, hF]
    by_cases hmn : m = n
    · subst hmn
      rw [← hPn, hκ]
      show 1 / betaB α β * Gn - Gn / (betaB α β * Pn) * Pn = 0
      field_simp
      ring
    · rw [ipJ_jT_orth α β (Ne.symm hmn), ipP_Q_orth α β D n m hn hm (Ne.symm hmn)]
      simp
  have h0 := key 0 (Nat.zero_le _)
  rw [hahnQ_at_zero, mul_one, Cop0_jT] at h0
  rw [key u hu, ← h0]

/-- The norm relation behind the singular values:
`‖jT_n‖²_{L²(ν_H)} = s_n² ‖Q_n‖²_{ℓ²(p_D)}`. -/
theorem norm_relation (α β D n : ℕ) (hn : n ≤ D) :
    (1 / betaB α β) * ipJ α β (jT α β n) (jT α β n) =
      singularSq α β D n * ipP α β D (hahnQ α β D n) (hahnQ α β D n) := by
  have hB := betaB_pos α β
  have hF := ipP_Cop α β D (jT_continuous α β n) (hahnQ α β D n)
  have e1 : ipP α β D (CopBeta α β D (jT α β n)) (hahnQ α β D n) =
      singularSq α β D n * ipP α β D (hahnQ α β D n) (hahnQ α β D n) := by
    unfold ipP
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Cop_jT α β D n hn (by simpa [Nat.lt_succ_iff] using hu)]; ring
  rw [← e1, hF]
  unfold ipJ
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Cstar_hahnQ α β D n hn]

lemma Cop_const_mul (α β D : ℕ) (c : ℝ) (f : ℝ → ℝ) (u : ℕ) :
    CopBeta α β D (fun t => c * f t) u = c * CopBeta α β D f u := by
  unfold CopBeta
  have e : ∀ t : ℝ, bern D u t * (c * f t) * wtJ α β t = c * (bern D u t * f t * wtJ α β t) :=
    fun t => by ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul]; ring

/-- The unit-normalised Jacobi mode `J_n` of `L²(ν_H)`. -/
noncomputable def Jmode (α β n : ℕ) (t : ℝ) : ℝ :=
  jT α β n t / Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n))

/-- The unit-normalised Hahn mode `H_n` of `ℓ²(p_D)`. -/
noncomputable def Hmode (α β D n : ℕ) (u : ℕ) : ℝ :=
  hahnQ α β D n u / Real.sqrt (ipP α β D (hahnQ α β D n) (hahnQ α β D n))

/-- **Singular pair relation of `prop:betabinomialpolar`**: for `0 ≤ n ≤ D`,
`T_D J_n = s_n H_n` on `{0,…,D}`, `s_n = √(D^{\underline n}/(D+α+β+2)_n) > 0`, where `J_n` and `H_n`
are the unit-normalised Jacobi and Hahn modes in `L²(ν_H)` and `ℓ²(p_D)`. -/
theorem singular_pair (α β D n : ℕ) (hn : n ≤ D) {u : ℕ} (hu : u ≤ D) :
    CopBeta α β D (Jmode α β n) u = Real.sqrt (singularSq α β D n) * Hmode α β D n u := by
  have hs := singularSq_pos α β D n hn
  have hP := ipP_Q_pos α β D n
  have hnr := norm_relation α β D n hn
  have hsqrt : Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n)) =
      Real.sqrt (singularSq α β D n) *
        Real.sqrt (ipP α β D (hahnQ α β D n) (hahnQ α β D n)) := by
    rw [hnr, Real.sqrt_mul hs.le]
  unfold Jmode Hmode
  have e : (fun t => jT α β n t / Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n))) =
      fun t => (Real.sqrt ((1 / betaB α β) * ipJ α β (jT α β n) (jT α β n)))⁻¹ * jT α β n t := by
    funext t; ring
  rw [e, Cop_const_mul, Cop_jT α β D n hn hu, hsqrt]
  have h1 : 0 < Real.sqrt (singularSq α β D n) := Real.sqrt_pos.2 hs
  have h2 : 0 < Real.sqrt (ipP α β D (hahnQ α β D n) (hahnQ α β D n)) := Real.sqrt_pos.2 hP
  have h3 := Real.sq_sqrt hs.le
  field_simp
  rw [h3]

/-- info: 'FormalResearch.Racah.beta01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms beta01

/-- info: 'FormalResearch.Racah.pD_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pD_eq_integral

/-- info: 'FormalResearch.Racah.ipJ_jT_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ipJ_jT_orth

/-- info: 'FormalResearch.Racah.ipJ_jT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ipJ_jT_pos

/-- info: 'FormalResearch.Racah.hahn_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_orth

/-- info: 'FormalResearch.Racah.hahn_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_determined

/-- info: 'FormalResearch.Racah.ipP_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ipP_Cop

/-- info: 'FormalResearch.Racah.chu_vandermonde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chu_vandermonde

/-- info: 'FormalResearch.Racah.Cop0_jT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cop0_jT

/-- info: 'FormalResearch.Racah.Cop_jT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cop_jT

/-- info: 'FormalResearch.Racah.norm_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_relation

/-- info: 'FormalResearch.Racah.singular_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms singular_pair

end FormalResearch.Racah
