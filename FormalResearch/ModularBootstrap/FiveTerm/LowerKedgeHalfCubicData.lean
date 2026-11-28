module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerKedgeHalfCubic

/-!
# Virasoro `HalfCubicData` Instances and `virPhiInv` (`cts:Kedge-signed`)

Constructs from `exists_virPolydisc` and `virasoroChart_holds`:
* `virQE`, `virQO`, `virQ` via `evenCauchy`/`oddCauchy` + `divQ`, proving `1 + (s^2 + a) virQ s a = virPhaseFactor s a`
  from the 1D complex identity theorem on `virPhaseFactor (±√(-a)) a = 1`;
* `virasoroHalfCubic : HalfCubicData` via `mkHalfCubicOfCauchy`, with `‖E_n(-a, a) - 1‖ = O(n⁻¹)` and `‖O_n(-a, a)‖ = O(n⁻¹)`;
* `virasoroHalfCubicAux : HalfCubicData` for `virPhaseFactor * (1 - 2 i virV)⁻¹ * virEb`, sharing the exact same
  `s₁`, `r_a`, and `ψ = virPsi` as `virasoroHalfCubic`;
* `virPhiInv` and `virasoroHalfCubic_uReal_virPhiInv`: `d.uReal c (virPhiInv c x).re = x`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.FineOrderSigned

noncomputable section

/-! ### 1. Packaged polydisc radii & Cauchy-divided remainder `virQ` -/

/-- Packaged polydisc and Cauchy splitting parameters for `virasoroHalfCubic` and `virasoroHalfCubicAux`. -/
structure VirPolydiscPack where
  r_s : ℝ
  r_a : ℝ
  M_G0 : ℝ
  M_aux : ℝ
  K_b : ℝ
  C_psi_diff : ℝ
  hrs : 0 < r_s
  hra : 0 < r_a
  hMG0 : 0 ≤ M_G0
  hMaux : 0 ≤ M_aux
  hKb : 0 ≤ K_b
  hCpd : 0 ≤ C_psi_diff
  h_ra_psi : r_a ≤ min ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.ρ_ψ / 2)
    ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.r_ψ / 2)
  hG_s : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => virPhaseFactor ζ a) (ball 0 r_s)
  hG_a : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (virPhaseFactor ζ) (ball 0 r_a)
  hG_bd : ∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖virPhaseFactor ζ a‖ ≤ M_G0
  hW_s : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => (1 - 2 * Complex.I * virV ζ a)⁻¹) (ball 0 r_s)
  hW_a : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (fun a => (1 - 2 * Complex.I * virV ζ a)⁻¹) (ball 0 r_a)
  hW_bd : ∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖(1 - 2 * Complex.I * virV ζ a)⁻¹‖ ≤ 2
  hVY_bd : ∀ ζ ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖virV ζ a‖ ≤ 1 / 4 ∧ ‖yVirC (virV ζ a)‖ ≤ 1 / 4
  hEb_s : ∀ n, 1 ≤ n → ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => virEb n ζ a) (ball 0 r_s)
  hEb_a : ∀ n, 1 ≤ n → ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (virEb n ζ) (ball 0 r_a)
  hEb_bd : ∀ n ζ a, 1 ≤ n → ζ ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a → ‖virEb n ζ a - 1‖ ≤ K_b * n⁻¹
  hPsi_diff : ∀ n, 2 ≤ n → ∀ a ∈ ball (0 : ℂ) r_a, ‖virPsi n a - virPsi 0 a‖ ≤ C_psi_diff * n ^ (-2 : ℝ)
  hsym : ∀ (x a : ℝ), |x| < r_s → |a| < r_a →
    (virV (x : ℂ) (a : ℂ)).im = 0 ∧ (virMGeo (x : ℂ) (a : ℂ)).im = 0 ∧
    (virThetaOutC (virV (x : ℂ) (a : ℂ))).im = 0 ∧
    virMGeo (-(x : ℂ)) (a : ℂ) = virMGeo (x : ℂ) (a : ℂ) ∧
    (yVirC (virV (x : ℂ) (a : ℂ))).im = 0 ∧
    (virPsi 0 (a : ℂ)).im = 0 ∧
    ∀ n, 1 ≤ n → (virPsi n (a : ℂ)).im = 0
  hsaddle : ∀ (a : ℝ), -r_a < a → a < 0 →
    virPhaseFactor (√(-a) : ℂ) (a : ℂ) = 1 ∧ virPhaseFactor (-(√(-a) : ℂ)) (a : ℂ) = 1

/-- Canonical choice of Virasoro polydisc parameters. -/
def virPoly : VirPolydiscPack :=
  let h := exists_virPolydisc
  let r_s := Classical.choose h
  let h1 := Classical.choose_spec h
  let r_a := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let M_G0 := Classical.choose h2
  let h3 := Classical.choose_spec h2
  let M_aux := Classical.choose h3
  let h4 := Classical.choose_spec h3
  let K_b := Classical.choose h4
  let h5 := Classical.choose_spec h4
  let C_psi_diff := Classical.choose h5
  let hs := Classical.choose_spec h5
  { r_s := r_s
    r_a := r_a
    M_G0 := M_G0
    M_aux := M_aux
    K_b := K_b
    C_psi_diff := C_psi_diff
    hrs := hs.1
    hra := hs.2.1
    hMG0 := hs.2.2.1
    hMaux := hs.2.2.2.1
    hKb := hs.2.2.2.2.1
    hCpd := hs.2.2.2.2.2.1
    h_ra_psi := hs.2.2.2.2.2.2.1
    hG_s := hs.2.2.2.2.2.2.2.1
    hG_a := hs.2.2.2.2.2.2.2.2.1
    hG_bd := hs.2.2.2.2.2.2.2.2.2.1
    hW_s := hs.2.2.2.2.2.2.2.2.2.2.1
    hW_a := hs.2.2.2.2.2.2.2.2.2.2.2.1
    hW_bd := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
    hVY_bd := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hEb_s := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hEb_a := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hEb_bd := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hPsi_diff := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hsym := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hsaddle := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }

/-- Outer Cauchy splitting radius `r₀ = virPoly.r_s / 2`. -/
def virR0Div : ℝ := virPoly.r_s / 2

/-- Quadratic Cauchy-division radius `r_q_div = virR0Div^2 / 4 < virR0Div^2 / 2`. -/
def virRqDiv : ℝ := virR0Div ^ 2 / 4

/-- Inner parameter radius `r_a_in = min virPoly.r_a (virRqDiv / 4)`. -/
def virRaIn : ℝ := min virPoly.r_a (virRqDiv / 4)

/-- Inner `s`-radius `r_s_in = min (virR0Div / 4) 1` satisfying `r_s_in^2 ≤ virRqDiv / 4 < virRqDiv / 2`. -/
def virRsIn : ℝ := min (virR0Div / 4) 1

lemma virR0Div_pos : 0 < virR0Div := half_pos virPoly.hrs
lemma virR0Div_lt : virR0Div < virPoly.r_s := half_lt_self virPoly.hrs
lemma virRqDiv_pos : 0 < virRqDiv := by have := virR0Div_pos; unfold virRqDiv; positivity
lemma virRqDiv_lt : virRqDiv < virR0Div ^ 2 / 2 := by
  unfold virRqDiv; linarith [sq_pos_of_pos virR0Div_pos]
lemma virRaIn_pos : 0 < virRaIn := lt_min virPoly.hra (div_pos virRqDiv_pos (by norm_num))
lemma virRsIn_pos : 0 < virRsIn := lt_min (by have := virR0Div_pos; positivity) one_pos

lemma virRsIn_lt_virR0Div : virRsIn < virR0Div := by
  have h1 : virRsIn ≤ virR0Div / 4 := min_le_left _ _
  linarith [virR0Div_pos]

lemma virRsIn_sq_le : virRsIn ^ 2 ≤ virRqDiv / 2 := by
  have h1 : 0 ≤ virRsIn := virRsIn_pos.le
  have h2 : virRsIn ≤ virR0Div / 4 := min_le_left _ _
  calc virRsIn ^ 2 ≤ (virR0Div / 4) ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = virRqDiv / 4 := by dsimp [virRqDiv]; ring
    _ ≤ virRqDiv / 2 := by linarith [virRqDiv_pos]

lemma virRaIn_le_rq : virRaIn ≤ virRqDiv / 4 := min_le_right _ _
lemma virRaIn_le_poly : virRaIn ≤ virPoly.r_a := min_le_left _ _

/-- Even Cauchy-divided part of `virPhaseFactor` around `q = -a`. -/
def virQE (q a : ℂ) : ℂ :=
  divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) q

/-- Odd Cauchy-divided part of `virPhaseFactor` around `q = -a`. -/
def virQO (q a : ℂ) : ℂ :=
  divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) q

/-- Holomorphic divided remainder `virQ(s, a) = virQE(s^2, a) + i s virQO(s^2, a)`
satisfying `1 + (s^2 + a) virQ(s, a) = virPhaseFactor(s, a)`. -/
def virQ (s a : ℂ) : ℂ := virQE (s ^ 2) a + Complex.I * s * virQO (s ^ 2) a

private lemma virPhaseFactor_ball_r0 : ∀ ζ ∈ sphere (0 : ℂ) virR0Div, ∀ a ∈ ball (0 : ℂ) virPoly.r_a,
    ‖virPhaseFactor ζ a‖ ≤ virPoly.M_G0 := fun ζ hζ a ha =>
  virPoly.hG_bd ζ (by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ]; exact virR0Div_lt) a ha

private lemma virPhaseFactor_sphere_rq : ∀ ζ ∈ sphere (0 : ℂ) virRqDiv, ∀ a ∈ ball (0 : ℂ) virRaIn,
    ‖evenCauchy virPhaseFactor virR0Div ζ a‖ ≤ 2 * virPoly.M_G0 ∧
    ‖oddCauchy virPhaseFactor virR0Div ζ a‖ ≤ (2 / virR0Div) * virPoly.M_G0 := by
  intro ζ hζ a ha
  have ha_poly : a ∈ ball (0 : ℂ) virPoly.r_a :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly)
  have hζ_ball : ζ ∈ ball (0 : ℂ) (virR0Div ^ 2 / 2) := by
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ]
    exact virRqDiv_lt
  exact ⟨evenCauchy_norm_le' virR0Div_pos hζ_ball fun w hw => virPhaseFactor_ball_r0 w hw a ha_poly,
    oddCauchy_norm_le virR0Div_pos hζ_ball fun w hw => virPhaseFactor_ball_r0 w hw a ha_poly⟩

/-- Diagonal Cauchy values vanish at the saddle `q = -a`:
`evenCauchy virPhaseFactor r₀ (-a) a = 1` and `oddCauchy virPhaseFactor r₀ (-a) a = 0`. -/
lemma virPhaseFactor_saddle_even_odd {a : ℂ} (ha : a ∈ ball (0 : ℂ) virRaIn) :
    evenCauchy virPhaseFactor virR0Div (-a) a = 1 ∧
    oddCauchy virPhaseFactor virR0Div (-a) a = 0 := by
  have hr₀ := virR0Div_pos
  have hr₀s := virR0Div_lt
  have ha_poly : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) virRaIn → z ∈ ball (0 : ℂ) virPoly.r_a := fun hz =>
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz).trans_le virRaIn_le_poly)
  have hden_lb : ∀ {ζ z : ℂ}, ζ ∈ sphere (0 : ℂ) virR0Div → z ∈ ball (0 : ℂ) virRaIn →
      virR0Div ^ 2 / 2 ≤ ‖ζ ^ 2 + z‖ := fun {ζ z} hζ hz => by
    have hζn : ‖ζ‖ = virR0Div := mem_sphere_zero_iff_norm.mp hζ
    have hsq : ‖ζ ^ 2‖ = virR0Div ^ 2 := by rw [norm_pow, hζn]
    have hzn : ‖z‖ < virR0Div ^ 2 / 2 := by
      have hz1 : ‖z‖ < virRaIn := mem_ball_zero_iff.mp hz
      have hz2 : virRaIn ≤ virR0Div ^ 2 / 16 := by
        dsimp [virRaIn, virRqDiv]; nlinarith [min_le_right virPoly.r_a (virR0Div ^ 2 / 4 / 4)]
      linarith [sq_pos_of_pos hr₀]
    have htri := norm_sub_norm_le (ζ ^ 2) (-z)
    rw [sub_neg_eq_add, norm_neg, hsq] at htri
    linarith
  have hden_ne : ∀ {ζ z : ℂ}, ζ ∈ sphere (0 : ℂ) virR0Div → z ∈ ball (0 : ℂ) virRaIn →
      ζ ^ 2 + z ≠ 0 := fun {ζ z} hζ hz =>
    norm_ne_zero_iff.mp (by linarith [sq_pos_of_pos hr₀, hden_lb hζ hz])
  have hE_diff : DifferentiableOn ℂ (fun z => evenCauchy virPhaseFactor virR0Div (-z) z) (ball 0 virRaIn) := by
    have heq : (fun z => evenCauchy virPhaseFactor virR0Div (-z) z) =
        fun z => (2 * π * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, virR0Div),
          (ζ / (ζ ^ 2 + z)) * virPhaseFactor ζ z := by
      ext z; unfold evenCauchy; simp only [sub_neg_eq_add, smul_eq_mul]
    rw [heq]
    refine differentiableOn_circleIntegral_param hr₀ (M := (2 / virR0Div) * virPoly.M_G0) ?_ ?_ ?_
    · intro z hz
      have hGc : ContinuousOn (fun ζ => virPhaseFactor ζ z) (sphere 0 virR0Div) :=
        (virPoly.hG_s z (ha_poly hz)).continuousOn.mono
          (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
      have hkc : ContinuousOn (fun ζ : ℂ => ζ / (ζ ^ 2 + z)) (sphere 0 virR0Div) :=
        continuousOn_id.div ((continuousOn_id.pow 2).add continuousOn_const) fun ζ hζ => hden_ne hζ hz
      exact hkc.mul hGc
    · intro ζ hζ
      have hζs : ζ ∈ ball (0 : ℂ) virPoly.r_s := by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ]; exact hr₀s
      have hdiv : DifferentiableOn ℂ (fun z => ζ / (ζ ^ 2 + z)) (ball 0 virRaIn) :=
        (differentiableOn_const ζ).div ((differentiableOn_const (ζ ^ 2)).add differentiableOn_id)
          fun z hz => hden_ne hζ hz
      exact hdiv.mul ((virPoly.hG_a ζ hζs).mono (ball_subset_ball virRaIn_le_poly))
    · intro ζ hζ z hz
      have hζn : ‖ζ‖ = virR0Div := mem_sphere_zero_iff_norm.mp hζ
      have hd := hden_lb hζ hz
      have hMG := virPhaseFactor_ball_r0 ζ hζ z (ha_poly hz)
      rw [norm_mul, norm_div, hζn]
      have hdiv : virR0Div / ‖ζ ^ 2 + z‖ ≤ 2 / virR0Div := by
        rw [div_le_div_iff₀ (by linarith [sq_pos_of_pos hr₀]) hr₀]; linarith
      exact mul_le_mul hdiv hMG (norm_nonneg _) (by positivity)
  have hO_diff : DifferentiableOn ℂ (fun z => oddCauchy virPhaseFactor virR0Div (-z) z) (ball 0 virRaIn) := by
    have heq : (fun z => oddCauchy virPhaseFactor virR0Div (-z) z) =
        fun z => (2 * π * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, virR0Div),
          (-Complex.I / (ζ ^ 2 + z)) * virPhaseFactor ζ z := by
      ext z; unfold oddCauchy; simp only [sub_neg_eq_add, smul_eq_mul]
    rw [heq]
    refine differentiableOn_circleIntegral_param hr₀ (M := (2 / virR0Div ^ 2) * virPoly.M_G0) ?_ ?_ ?_
    · intro z hz
      have hGc : ContinuousOn (fun ζ => virPhaseFactor ζ z) (sphere 0 virR0Div) :=
        (virPoly.hG_s z (ha_poly hz)).continuousOn.mono
          (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀s))
      have hkc : ContinuousOn (fun ζ : ℂ => -Complex.I / (ζ ^ 2 + z)) (sphere 0 virR0Div) :=
        continuousOn_const.div ((continuousOn_id.pow 2).add continuousOn_const) fun ζ hζ => hden_ne hζ hz
      exact hkc.mul hGc
    · intro ζ hζ
      have hζs : ζ ∈ ball (0 : ℂ) virPoly.r_s := by
        rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ]; exact hr₀s
      have hdiv : DifferentiableOn ℂ (fun z => -Complex.I / (ζ ^ 2 + z)) (ball 0 virRaIn) :=
        (differentiableOn_const _).div ((differentiableOn_const (ζ ^ 2)).add differentiableOn_id)
          fun z hz => hden_ne hζ hz
      exact hdiv.mul ((virPoly.hG_a ζ hζs).mono (ball_subset_ball virRaIn_le_poly))
    · intro ζ hζ z hz
      have hd := hden_lb hζ hz
      have hMG := virPhaseFactor_ball_r0 ζ hζ z (ha_poly hz)
      rw [norm_mul, norm_div, norm_neg, Complex.norm_I]
      have hdiv : 1 / ‖ζ ^ 2 + z‖ ≤ 2 / virR0Div ^ 2 := by
        rw [div_le_div_iff₀ (by linarith [sq_pos_of_pos hr₀]) (sq_pos_of_pos hr₀)]; linarith
      exact mul_le_mul hdiv hMG (norm_nonneg _) (by positivity)
  have h_real_neg : ∀ (x : ℝ), -virRaIn < x → x < 0 →
      evenCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 1 ∧
      oddCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 0 := fun x hxlo hx0 => by
    have hxC : (x : ℂ) ∈ ball (0 : ℂ) virPoly.r_a :=
      ha_poly (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx0]; linarith)
    have hsr_lt : √(-x) < virR0Div := by
      have hnegx : -x < virR0Div ^ 2 := by
        have h1 : -x < virRaIn := by linarith
        have h2 : virRaIn ≤ virR0Div ^ 2 / 16 := by
          dsimp [virRaIn, virRqDiv]; nlinarith [min_le_right virPoly.r_a (virR0Div ^ 2 / 4 / 4)]
        linarith [sq_pos_of_pos hr₀]
      calc √(-x) < √(virR0Div ^ 2) := Real.sqrt_lt_sqrt (by linarith) hnegx
        _ = virR0Div := Real.sqrt_sq hr₀.le
    have hsn : ‖(√(-x) : ℂ)‖ < virR0Div := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hsr_lt
    have hp := evenCauchy_add_oddCauchy hr₀ hr₀s (virPoly.hG_s (x : ℂ) hxC) hsn
    have hm := evenCauchy_sub_oddCauchy hr₀ hr₀s (virPoly.hG_s (x : ℂ) hxC) hsn
    have hsqC : (√(-x) : ℂ) ^ 2 = -(x : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith), Complex.ofReal_neg]
    have hsad := virPoly.hsaddle x (by linarith [virRaIn_le_poly] : -virPoly.r_a < x) hx0
    rw [hsqC, hsad.1] at hp
    rw [hsqC, hsad.2] at hm
    have hE1 : evenCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 1 := by
      have h2 : 2 * evenCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 2 * 1 := by
        linear_combination hp + hm
      exact mul_left_cancel₀ two_ne_zero h2
    have hO0 : oddCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 0 := by
      have hs_ne : (2 * Complex.I * (√(-x) : ℂ)) ≠ 0 := by
        simp [Complex.ofReal_eq_zero, (Real.sqrt_pos.mpr (neg_pos.mpr hx0)).ne']
      have h2 : (2 * Complex.I * (√(-x) : ℂ)) *
          oddCauchy virPhaseFactor virR0Div (-(x : ℂ)) (x : ℂ) = 0 := by
        linear_combination hp - hm
      exact (mul_eq_zero.mp h2).resolve_left hs_ne
    exact ⟨hE1, hO0⟩
  let z₀ : ℂ := ((-virRaIn / 2 : ℝ) : ℂ)
  have hz₀ : z₀ ∈ ball (0 : ℂ) virRaIn := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith [virRaIn_pos])]
    linarith [virRaIn_pos]
  let x_seq : ℕ → ℝ := fun k => -virRaIn / 2 + (virRaIn / 4) / ((k : ℝ) + 1)
  have hx_tend : Tendsto (fun k : ℕ => (x_seq k : ℂ)) atTop (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto x_seq atTop (𝓝 (-virRaIn / 2)) := by
        have ht : Tendsto (fun k : ℕ => (virRaIn / 4) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          (tendsto_const_nhds (x := virRaIn / 4)).div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa [x_seq] using (tendsto_const_nhds (x := -virRaIn / 2)).add ht
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp h0
    · refine Eventually.of_forall fun k => ?_
      dsimp [z₀]
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      have hk_pos : 0 < (virRaIn / 4) / ((k : ℝ) + 1) := div_pos (by linarith [virRaIn_pos]) (by positivity)
      dsimp [x_seq]; linarith
  have hx_in : ∀ k : ℕ, -virRaIn < x_seq k ∧ x_seq k < 0 := fun k => by
    have hk_pos : 0 < (virRaIn / 4) / ((k : ℝ) + 1) := div_pos (by linarith [virRaIn_pos]) (by positivity)
    have hk_le : (virRaIn / 4) / ((k : ℝ) + 1) ≤ virRaIn / 4 :=
      div_le_self (by linarith [virRaIn_pos]) (by linarith)
    dsimp [x_seq]; constructor <;> linarith [virRaIn_pos]
  have hfreq_E : ∃ᶠ z in 𝓝[≠] z₀, evenCauchy virPhaseFactor virR0Div (-z) z = (1 : ℂ) :=
    hx_tend.frequently ((Filter.Eventually.of_forall (f := atTop) fun k =>
      (h_real_neg (x_seq k) (hx_in k).1 (hx_in k).2).1).frequently)
  have hfreq_O : ∃ᶠ z in 𝓝[≠] z₀, oddCauchy virPhaseFactor virR0Div (-z) z = (0 : ℂ) :=
    hx_tend.frequently ((Filter.Eventually.of_forall (f := atTop) fun k =>
      (h_real_neg (x_seq k) (hx_in k).1 (hx_in k).2).2).frequently)
  exact ⟨(hE_diff.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (fun _ _ => analyticAt_const) (convex_ball (0 : ℂ) virRaIn).isPreconnected hz₀ hfreq_E ha,
    (hO_diff.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (fun _ _ => analyticAt_const) (convex_ball (0 : ℂ) virRaIn).isPreconnected hz₀ hfreq_O ha⟩

/-- Polynomial division identity `1 + (s^2 + a) * virQ s a = virPhaseFactor s a`
on `s ∈ ball 0 virRsIn`, `a ∈ ball 0 virRaIn`. -/
lemma virQ_eq {s a : ℂ} (hs : s ∈ ball (0 : ℂ) virRsIn) (ha : a ∈ ball (0 : ℂ) virRaIn) :
    1 + (s ^ 2 + a) * virQ s a = virPhaseFactor s a := by
  have ha_poly : a ∈ ball (0 : ℂ) virPoly.r_a :=
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly)
  have hs_r0 : ‖s‖ < virR0Div := lt_trans (mem_ball_zero_iff.mp hs) virRsIn_lt_virR0Div
  have ha_rq : -a ∈ ball (0 : ℂ) virRqDiv := by
    rw [mem_ball_zero_iff, norm_neg]
    exact (mem_ball_zero_iff.mp ha).trans_le (by linarith [virRaIn_le_rq, virRqDiv_pos])
  have hs2_rq : s ^ 2 ∈ ball (0 : ℂ) virRqDiv := by
    rw [mem_ball_zero_iff, norm_pow]
    have hs1 : ‖s‖ ^ 2 < virRsIn ^ 2 :=
      pow_lt_pow_left₀ (mem_ball_zero_iff.mp hs) (norm_nonneg _) two_ne_zero
    linarith [virRsIn_sq_le, virRqDiv_pos]
  have hE_diff : DifferentiableOn ℂ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a)
      (ball 0 (virR0Div ^ 2 / 2)) :=
    differentiableOn_evenCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0 ha_poly
  have hO_diff : DifferentiableOn ℂ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a)
      (ball 0 (virR0Div ^ 2 / 2)) :=
    differentiableOn_oddCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0 ha_poly
  have hdivE := divQ_eq virRqDiv_pos virRqDiv_lt hE_diff ha_rq hs2_rq
  have hdivO := divQ_eq virRqDiv_pos virRqDiv_lt hO_diff ha_rq hs2_rq
  have ⟨hE1, hO0⟩ := virPhaseFactor_saddle_even_odd ha
  have hrec := evenCauchy_add_oddCauchy virR0Div_pos virR0Div_lt (virPoly.hG_s a ha_poly) hs_r0
  unfold virQ virQE virQO
  rw [hE1] at hdivE
  rw [hO0] at hdivO
  have hE2 : evenCauchy virPhaseFactor virR0Div (s ^ 2) a =
      1 + (s ^ 2 + a) * divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2) := by
    linear_combination hdivE
  have hO2 : oddCauchy virPhaseFactor virR0Div (s ^ 2) a =
      (s ^ 2 + a) * divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2) := by
    linear_combination hdivO
  calc 1 + (s ^ 2 + a) * (divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2) +
          Complex.I * s * divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2))
      = (1 + (s ^ 2 + a) * divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2)) +
          Complex.I * s * ((s ^ 2 + a) * divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (s ^ 2)) := by
          ring
    _ = evenCauchy virPhaseFactor virR0Div (s ^ 2) a + Complex.I * s * oddCauchy virPhaseFactor virR0Div (s ^ 2) a := by
          rw [← hE2, ← hO2]
    _ = virPhaseFactor s a := hrec

private lemma virQ_properties : ∃ M_Q : ℝ, 0 ≤ M_Q ∧
    (∀ a ∈ ball (0 : ℂ) virRaIn, DifferentiableOn ℂ (fun ζ => virQ ζ a) (ball 0 virRsIn)) ∧
    (∀ ζ ∈ ball (0 : ℂ) virRsIn, DifferentiableOn ℂ (virQ ζ) (ball 0 virRaIn)) ∧
    (∀ ζ ∈ ball (0 : ℂ) virRsIn, ∀ a ∈ ball (0 : ℂ) virRaIn, ‖virQ ζ a‖ ≤ M_Q) := by
  let r_c : ℝ := virRqDiv / 2
  have hrc_lt : r_c < virRqDiv := half_lt_self virRqDiv_pos
  let M_Q : ℝ := virRqDiv * (2 * virPoly.M_G0) / (virRqDiv - r_c) ^ 2 +
    virRsIn * (virRqDiv * ((2 / virR0Div) * virPoly.M_G0) / (virRqDiv - r_c) ^ 2)
  have hMQ_nn : 0 ≤ M_Q := by
    have := virRqDiv_pos; have := virPoly.hMG0; have := virRsIn_pos; have := virR0Div_pos
    positivity
  refine ⟨M_Q, hMQ_nn, ?_, ?_, ?_⟩
  · intro a ha
    have ha_poly : a ∈ ball (0 : ℂ) virPoly.r_a :=
      mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly)
    have ha_rq : -a ∈ ball (0 : ℂ) virRqDiv := by
      rw [mem_ball_zero_iff, norm_neg]
      exact (mem_ball_zero_iff.mp ha).trans_le (by linarith [virRaIn_le_rq, virRqDiv_pos])
    have hE_diff := differentiableOn_evenCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0 ha_poly
    have hO_diff := differentiableOn_oddCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0 ha_poly
    have hdE := differentiableOn_divQ_fst virRqDiv_pos virRqDiv_lt hE_diff ha_rq
    have hdO := differentiableOn_divQ_fst virRqDiv_pos virRqDiv_lt hO_diff ha_rq
    intro ζ hζ
    have hζ2 : ζ ^ 2 ∈ ball (0 : ℂ) virRqDiv := by
      rw [mem_ball_zero_iff, norm_pow]
      have := pow_lt_pow_left₀ (mem_ball_zero_iff.mp hζ) (norm_nonneg _) two_ne_zero
      linarith [virRsIn_sq_le, virRqDiv_pos]
    have hsq_d : DifferentiableAt ℂ (fun z : ℂ => z ^ 2) ζ := differentiableAt_id.pow 2
    exact (((hdE.differentiableAt (isOpen_ball.mem_nhds hζ2)).comp
      (g := fun q => divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) q)
      (f := fun z : ℂ => z ^ 2) ζ hsq_d).add
      ((differentiableAt_id.const_mul Complex.I).mul
        ((hdO.differentiableAt (isOpen_ball.mem_nhds hζ2)).comp
          (g := fun q => divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) q)
          (f := fun z : ℂ => z ^ 2) ζ hsq_d))).differentiableWithinAt
  · intro ζ hζ
    have hζ2_bd : ∀ a ∈ ball (0 : ℂ) virRaIn, ‖ζ ^ 2‖ ≤ r_c := fun _ _ => by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hζ).le 2).trans virRsIn_sq_le
    have ha_bd : ∀ a ∈ ball (0 : ℂ) virRaIn, ‖-a‖ ≤ r_c := fun a ha => by
      rw [norm_neg]
      exact (mem_ball_zero_iff.mp ha).le.trans (virRaIn_le_rq.trans (by dsimp [r_c]; linarith [virRqDiv_pos]))
    have hHq_E : ∀ a ∈ ball (0 : ℂ) virRaIn,
        DifferentiableOn ℂ (fun w => evenCauchy virPhaseFactor virR0Div w a) (ball 0 (virR0Div ^ 2 / 2)) :=
      fun a ha => differentiableOn_evenCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0
        (mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly))
    have hHa_E : ∀ w ∈ sphere (0 : ℂ) virRqDiv,
        DifferentiableOn ℂ (fun a => evenCauchy virPhaseFactor virR0Div w a) (ball 0 virRaIn) := fun w hw =>
      (differentiableOn_evenCauchy_a virR0Div_pos virR0Div_lt virPoly.hG_s virPoly.hG_a virPhaseFactor_ball_r0
        (by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hw]; exact virRqDiv_lt)).mono
        (ball_subset_ball virRaIn_le_poly)
    have hHq_O : ∀ a ∈ ball (0 : ℂ) virRaIn,
        DifferentiableOn ℂ (fun w => oddCauchy virPhaseFactor virR0Div w a) (ball 0 (virR0Div ^ 2 / 2)) :=
      fun a ha => differentiableOn_oddCauchy_q virR0Div_pos virR0Div_lt virPoly.hG_s virPhaseFactor_ball_r0
        (mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly))
    have hHa_O : ∀ w ∈ sphere (0 : ℂ) virRqDiv,
        DifferentiableOn ℂ (fun a => oddCauchy virPhaseFactor virR0Div w a) (ball 0 virRaIn) := fun w hw =>
      (differentiableOn_oddCauchy_a virR0Div_pos virR0Div_lt virPoly.hG_s virPoly.hG_a virPhaseFactor_ball_r0
        (by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hw]; exact virRqDiv_lt)).mono
        (ball_subset_ball virRaIn_le_poly)
    have hdE := differentiableOn_divQ_param virRqDiv_pos virRqDiv_lt hrc_lt hHq_E hHa_E
      (fun w hw a ha => (virPhaseFactor_sphere_rq w hw a ha).1)
      differentiableOn_id.neg ha_bd (differentiableOn_const (ζ ^ 2)) hζ2_bd
    have hdO := differentiableOn_divQ_param virRqDiv_pos virRqDiv_lt hrc_lt hHq_O hHa_O
      (fun w hw a ha => (virPhaseFactor_sphere_rq w hw a ha).2)
      differentiableOn_id.neg ha_bd (differentiableOn_const (ζ ^ 2)) hζ2_bd
    exact hdE.add ((differentiableOn_const (Complex.I * ζ)).mul hdO)
  · intro ζ hζ a ha
    have hζ_le : ‖ζ‖ ≤ virRsIn := (mem_ball_zero_iff.mp hζ).le
    have hζ2_le : ‖ζ ^ 2‖ ≤ r_c := by
      rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hζ_le 2).trans virRsIn_sq_le
    have ha_le : ‖-a‖ ≤ r_c := by
      rw [norm_neg]
      exact (mem_ball_zero_iff.mp ha).le.trans (virRaIn_le_rq.trans (by dsimp [r_c]; linarith [virRqDiv_pos]))
    have hbdE := norm_divQ_le virRqDiv_pos hrc_lt
      (fun w hw => (virPhaseFactor_sphere_rq w hw a ha).1) ha_le hζ2_le
    have hbdO := norm_divQ_le virRqDiv_pos hrc_lt
      (fun w hw => (virPhaseFactor_sphere_rq w hw a ha).2) ha_le hζ2_le
    unfold virQ virQE virQO
    calc ‖divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2) +
            Complex.I * ζ * divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2)‖
        ≤ ‖divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2)‖ +
            ‖ζ‖ * ‖divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2)‖ := by
          simpa [norm_mul, Complex.norm_I] using norm_add_le
            (divQ (fun ζ => evenCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2))
            (Complex.I * ζ * divQ (fun ζ => oddCauchy virPhaseFactor virR0Div ζ a) virRqDiv (-a) (ζ ^ 2))
      _ ≤ virRqDiv * (2 * virPoly.M_G0) / (virRqDiv - r_c) ^ 2 +
            virRsIn * (virRqDiv * ((2 / virR0Div) * virPoly.M_G0) / (virRqDiv - r_c) ^ 2) := by
          have := virRsIn_pos.le; gcongr

/-! ### 2. `virasoroHalfCubic` and `virasoroHalfCubicAux` (`HalfCubicData`) -/

private lemma virPhaseFactor_eb_symm (n : ℝ) (hn : 1 ≤ n) (x a : ℝ) (hx : |x| < virPoly.r_s)
    (ha : |a| < virPoly.r_a) :
    virPhaseFactor (-(x : ℂ)) (a : ℂ) * virEb n (-(x : ℂ)) (a : ℂ) =
      starRingEnd ℂ (virPhaseFactor (x : ℂ) (a : ℂ) * virEb n (x : ℂ) (a : ℂ)) := by
  obtain ⟨hV_im, hMG_im, hTh_im, hMG_even, hY_im, hPsi0_im, hPsin_im⟩ := virPoly.hsym x a hx ha
  have hMGs : virMGeo (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (virMGeo (x : ℂ) (a : ℂ)) := by
    rw [hMG_even, Complex.conj_eq_iff_im.mpr hMG_im]
  have hVs : virV (-(x : ℂ)) (a : ℂ) = -virV (x : ℂ) (a : ℂ) := virV_neg _ _
  have hYs : yVirC (virV (-(x : ℂ)) (a : ℂ)) = -yVirC (virV (x : ℂ) (a : ℂ)) := by
    rw [hVs, yVirC_neg]
  have hThs : virThetaOutC (virV (-(x : ℂ)) (a : ℂ)) = -virThetaOutC (virV (x : ℂ) (a : ℂ)) := by
    rw [hVs, virThetaOutC_neg]
  have hPhase_im0 : (virThetaOutC (virV (x : ℂ) (a : ℂ)) - (x : ℂ) * virPsi 0 (a : ℂ)).im = 0 := by
    simp [Complex.sub_im, Complex.mul_im, hTh_im, hPsi0_im]
  have hExpG : Complex.exp (Complex.I * (virThetaOutC (virV (-(x : ℂ)) (a : ℂ)) - -(x : ℂ) * virPsi 0 (a : ℂ))) =
      starRingEnd ℂ (Complex.exp (Complex.I * (virThetaOutC (virV (x : ℂ) (a : ℂ)) - (x : ℂ) * virPsi 0 (a : ℂ)))) := by
    rw [hThs, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_eq_iff_im.mpr hPhase_im0]
    ring
  have hG_sym : virPhaseFactor (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (virPhaseFactor (x : ℂ) (a : ℂ)) := by
    unfold virPhaseFactor; rw [map_mul, hMGs, hExpG]
  have hEb_sym : virEb n (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (virEb n (x : ℂ) (a : ℂ)) := by
    by_cases hn2 : 2 ≤ n
    · have hmt : lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV (-(x : ℂ)) (a : ℂ))) =
          starRingEnd ℂ (lowerMt (n ^ (-2 : ℝ)) (Complex.I * yVirC (virV (x : ℂ) (a : ℂ)))) := by
        unfold lowerMt
        simp only [hYs, map_div₀, map_mul, map_add, map_pow, map_one, Complex.conj_ofReal,
          Complex.conj_I, Complex.conj_eq_iff_im.mpr hY_im]
        ring_nf
      have hdiff_im : (virPsi n (a : ℂ) - virPsi 0 (a : ℂ)).im = 0 := by
        simp [Complex.sub_im, hPsin_im n hn, hPsi0_im]
      have hexp : Complex.exp (-Complex.I * -(x : ℂ) * (virPsi n (a : ℂ) - virPsi 0 (a : ℂ))) =
          starRingEnd ℂ (Complex.exp (-Complex.I * (x : ℂ) * (virPsi n (a : ℂ) - virPsi 0 (a : ℂ)))) := by
        rw [← Complex.exp_conj]
        congr 1
        rw [map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
          Complex.conj_eq_iff_im.mpr hdiff_im]
        ring
      unfold virEb
      simp only [hn2, ↓reduceIte, map_mul, map_pow, hmt, hexp]
    · unfold virEb; simp [hn2]
  rw [map_mul, hG_sym, hEb_sym]

/-- Principal `HalfCubicData` for Virasoro `(cts:Kedge-signed)`. -/
theorem virasoroHalfCubic_exists : ∃ d : HalfCubicData,
    d.r_a = min virRaIn ((virRsIn / 2) ^ 2 / 4) ∧
    d.s₁ = virRsIn / 4 ∧
    d.r_q = (virRsIn / 2) ^ 2 / 2 ∧
    d.ψ = virPsi ∧
    (∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖s‖ < virRsIn / 2 →
      d.B n a s = virPhaseFactor s a * virEb n s a) ∧
    (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.E n (-a) a - 1‖ ≤ virPoly.K_b * n⁻¹) ∧
    (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.O n (-a) a‖ ≤ (4 / (3 * (virRsIn / 2))) * virPoly.K_b * n⁻¹) := by
  obtain ⟨M_Q, hMQ, hQ_s, hQ_a, hQ_bd⟩ := virQ_properties
  have hK := virPsi_scale_pos
  have hψ_a : ∀ n, 1 ≤ n → DifferentiableOn ℂ (virPsi n) (ball 0 virRaIn) := fun n hn => by
    by_cases hn2 : 2 ≤ n
    · have hε0 : 0 ≤ n ^ (-2 : ℝ) := by positivity
      have hε1 : n ^ (-2 : ℝ) ≤ 1 / 4 := by
        have h1 : n ^ (-2 : ℝ) = (n ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
        rw [h1, one_div, inv_le_inv₀ (by positivity) (by norm_num)]; nlinarith
      have hspec := (chartParams.hψ_spec _ hε0 hε1).1
      intro a ha
      have ha_rho : (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a) ∈ ball (0 : ℂ) chartParams.ρ_ψ := by
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK)]
        have ha1 : ‖a‖ < virRaIn := mem_ball_zero_iff.mp ha
        have ha2 : virRaIn ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.ρ_ψ / 2 :=
          virRaIn_le_poly.trans (virPoly.h_ra_psi.trans (min_le_left _ _))
        have h3 := mul_lt_mul_of_pos_left (ha1.trans_le ha2) (inv_pos.mpr hK)
        rw [show ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ * ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.ρ_ψ / 2) =
            chartParams.ρ_ψ / 2 by field_simp [betaTip_pos.ne'] ] at h3
        linarith [lt_trans chartParams.hrψ_pos chartParams.hrψ_lt]
      have hd := hspec.differentiableAt (isOpen_ball.mem_nhds ha_rho)
      exact ((hd.comp a (differentiableAt_id.const_mul _)).const_mul _).differentiableWithinAt
    · have hε_gt : ¬ (0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4) := by
        intro ⟨_, hle⟩
        have h1 : n ^ (-2 : ℝ) = (n ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith), Real.rpow_natCast]
        rw [h1, one_div, inv_le_inv₀ (by positivity) (by norm_num)] at hle; nlinarith
      have hzero : virPsi n = fun _ => 0 := by
        ext a; unfold virPsi virasoroPsiEps; simp only [hε_gt, ↓reduceIte, mul_zero]
      rw [hzero]; exact differentiableOn_const 0
  let M_ψ' : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.M_ψ
  have hMψ' : 0 ≤ M_ψ' := mul_nonneg hK.le chartParams.hMψ_nn
  have hψ_bd : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) virRaIn → ‖virPsi n a‖ ≤ M_ψ' := fun n a _hn ha => by
    by_cases hε : 0 ≤ n ^ (-2 : ℝ) ∧ n ^ (-2 : ℝ) ≤ 1 / 4
    · have hspec := (chartParams.hψ_spec _ hε.1 hε.2).2.2.1
      have ha_r : (((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) * a) ∈ closedBall (0 : ℂ) chartParams.r_ψ := by
        rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hK)]
        have ha1 : ‖a‖ ≤ virRaIn := (mem_ball_zero_iff.mp ha).le
        have ha2 : virRaIn ≤ (2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.r_ψ / 2 :=
          virRaIn_le_poly.trans (virPoly.h_ra_psi.trans (min_le_right _ _))
        have h3 := mul_le_mul_of_nonneg_left (ha1.trans ha2) (inv_pos.mpr hK).le
        rw [show ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ * ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip * chartParams.r_ψ / 2) =
            chartParams.r_ψ / 2 by field_simp [betaTip_pos.ne'] ] at h3
        linarith [chartParams.hrψ_pos]
      unfold virPsi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
      exact mul_le_mul_of_nonneg_left (hspec _ ha_r).1 hK.le
    · unfold virPsi virasoroPsiEps; simp only [hε, ↓reduceIte, mul_zero, norm_zero]; exact hMψ'
  have ha_sub : ∀ {a : ℂ}, a ∈ ball (0 : ℂ) virRaIn → a ∈ ball (0 : ℂ) virPoly.r_a := fun ha =>
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le virRaIn_le_poly)
  have hs_sub : ∀ {ζ : ℂ}, ζ ∈ ball (0 : ℂ) virRsIn → ζ ∈ ball (0 : ℂ) virPoly.r_s := fun hζ =>
    mem_ball_zero_iff.mpr (lt_trans (mem_ball_zero_iff.mp hζ) (virRsIn_lt_virR0Div.trans virR0Div_lt))
  obtain ⟨d, hra_eq, hs1_eq, hrq_eq, hpsi_eq, hB_eq, hE_bd, hO_bd⟩ := mkHalfCubicOfCauchy
    virRsIn_pos virRaIn_pos hMQ hMψ' virPoly.hKb virQ virEb virPsi
    hQ_s hQ_a hQ_bd
    (fun n a hn ha => (virPoly.hEb_s n hn a (ha_sub ha)).mono (ball_subset_ball (virRsIn_lt_virR0Div.le.trans virR0Div_lt.le)))
    (fun n ζ hn hζ => (virPoly.hEb_a n hn ζ (hs_sub hζ)).mono (ball_subset_ball virRaIn_le_poly))
    (fun n ζ a hn hζ ha => virPoly.hEb_bd n ζ a hn (hs_sub hζ) (ha_sub ha))
    hψ_a hψ_bd
    (fun n a hn ha => (virPoly.hsym 0 a (by simpa using virPoly.hrs) (ha.trans_le virRaIn_le_poly)).2.2.2.2.2.2 n hn)
    (fun n x a hn hx ha => by
      have hxC : (x : ℂ) ∈ ball (0 : ℂ) virRsIn := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hx
      have hnxC : -(x : ℂ) ∈ ball (0 : ℂ) virRsIn := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hx
      have haC : (a : ℂ) ∈ ball (0 : ℂ) virRaIn := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using ha
      rw [virQ_eq hxC haC]
      have heq_neg := virQ_eq hnxC haC
      rw [show (-(x : ℂ)) ^ 2 + (a : ℂ) = (-(x : ℂ)) ^ 2 + (a : ℂ) from rfl] at heq_neg
      rw [heq_neg]
      exact virPhaseFactor_eb_symm n hn x a (hx.trans (virRsIn_lt_virR0Div.trans virR0Div_lt))
        (ha.trans_le virRaIn_le_poly))
  refine ⟨d, hra_eq, hs1_eq, hrq_eq, hpsi_eq, fun n a s hn ha hs => ?_, hE_bd, hO_bd⟩
  have hs_ball : s ∈ ball (0 : ℂ) virRsIn := by
    rw [mem_ball_zero_iff]; linarith [virRsIn_pos]
  have ha_ball : a ∈ ball (0 : ℂ) virRaIn := by
    rw [hra_eq, mem_ball_zero_iff] at ha
    exact mem_ball_zero_iff.mpr (ha.trans_le (min_le_left _ _))
  rw [hB_eq n a s hn ha hs, virQ_eq hs_ball ha_ball]

/-- Canonical principal `HalfCubicData` for Virasoro `(cts:Kedge-signed)`. -/
def virasoroHalfCubic : HalfCubicData := Classical.choose virasoroHalfCubic_exists

/-- Specification of `virasoroHalfCubic`. -/
lemma virasoroHalfCubic_spec :
    virasoroHalfCubic.r_a = min virRaIn ((virRsIn / 2) ^ 2 / 4) ∧
    virasoroHalfCubic.s₁ = virRsIn / 4 ∧
    virasoroHalfCubic.r_q = (virRsIn / 2) ^ 2 / 2 ∧
    virasoroHalfCubic.ψ = virPsi ∧
    (∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) virasoroHalfCubic.r_a → ‖s‖ < virRsIn / 2 →
      virasoroHalfCubic.B n a s = virPhaseFactor s a * virEb n s a) ∧
    (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) virasoroHalfCubic.r_a →
      ‖virasoroHalfCubic.E n (-a) a - 1‖ ≤ virPoly.K_b * n⁻¹) ∧
    (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) virasoroHalfCubic.r_a →
      ‖virasoroHalfCubic.O n (-a) a‖ ≤ (4 / (3 * (virRsIn / 2))) * virPoly.K_b * n⁻¹) :=
  Classical.choose_spec virasoroHalfCubic_exists

/-- Auxiliary holomorphic amplitude `B_aux n s a = G₀(s,a) * (1 - 2i V(s,a))⁻¹ * Eb_n(s,a)`
used for the `O(c⁻¹)` boundary correction in `virasoroKedge1Eps`. -/
def virBaux (n : ℝ) (s a : ℂ) : ℂ :=
  virPhaseFactor s a * (1 - 2 * Complex.I * virV s a)⁻¹ * virEb n s a

private def virMauxBound : ℝ := virPoly.M_G0 * 2 * (1 + virPoly.K_b)

private lemma virBaux_norm_le {n : ℝ} (hn : 1 ≤ n) {ζ a : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) virPoly.r_s) (ha : a ∈ ball (0 : ℂ) virPoly.r_a) :
    ‖virBaux n ζ a‖ ≤ virMauxBound := by
  have hEb : ‖virEb n ζ a‖ ≤ 1 + virPoly.K_b := by
    have h1 := virPoly.hEb_bd n ζ a hn hζ ha
    have hn1 : n⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn
    have h2 : virPoly.K_b * n⁻¹ ≤ virPoly.K_b * 1 := mul_le_mul_of_nonneg_left hn1 virPoly.hKb
    have htri := norm_sub_norm_le (virEb n ζ a) (1 : ℂ)
    rw [norm_one] at htri
    linarith
  have hG := virPoly.hG_bd ζ hζ a ha
  have hW := virPoly.hW_bd ζ hζ a ha
  unfold virBaux virMauxBound
  rw [norm_mul, norm_mul]
  have := virPoly.hMG0; have := virPoly.hKb
  gcongr

private lemma virBaux_symm (n : ℝ) (hn : 1 ≤ n) (x a : ℝ)
    (hx : |x| < virPoly.r_s) (ha : |a| < virPoly.r_a) :
    virBaux n (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (virBaux n (x : ℂ) (a : ℂ)) := by
  have hVim := (virPoly.hsym x a hx ha).1
  have hVneg : virV (-(x : ℂ)) (a : ℂ) = -virV (x : ℂ) (a : ℂ) := virV_neg _ _
  have hW_sym : (1 - 2 * Complex.I * virV (-(x : ℂ)) (a : ℂ))⁻¹ =
      starRingEnd ℂ ((1 - 2 * Complex.I * virV (x : ℂ) (a : ℂ))⁻¹) := by
    rw [hVneg, map_inv₀, map_sub, map_one, map_mul, map_mul, map_ofNat, Complex.conj_I,
      Complex.conj_eq_iff_im.mpr hVim]
    ring_nf
  have hGE := virPhaseFactor_eb_symm n hn x a hx ha
  unfold virBaux
  rw [show virPhaseFactor (-(x : ℂ)) (a : ℂ) * (1 - 2 * Complex.I * virV (-(x : ℂ)) (a : ℂ))⁻¹ *
      virEb n (-(x : ℂ)) (a : ℂ) =
      (virPhaseFactor (-(x : ℂ)) (a : ℂ) * virEb n (-(x : ℂ)) (a : ℂ)) *
        (1 - 2 * Complex.I * virV (-(x : ℂ)) (a : ℂ))⁻¹ by ring,
    hGE, hW_sym, ← map_mul]
  congr 1; ring

/-- Auxiliary `HalfCubicData` sharing `s₁`, `r_a`, and `ψ = virPsi` with `virasoroHalfCubic`. -/
theorem virasoroHalfCubicAux_exists : ∃ d_aux : HalfCubicData,
    d_aux.r_a = virasoroHalfCubic.r_a ∧
    d_aux.s₁ = virasoroHalfCubic.s₁ ∧
    d_aux.ψ = virasoroHalfCubic.ψ ∧
    (∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) d_aux.r_a → ‖s‖ < virRsIn / 2 →
      d_aux.B n a s = virBaux n s a) := by
  let r_q_aux : ℝ := virR0Div ^ 2 / 2
  let r_a_aux : ℝ := virasoroHalfCubic.r_a
  let s₁_aux : ℝ := virasoroHalfCubic.s₁
  have hra_eq : r_a_aux = min virRaIn ((virRsIn / 2) ^ 2 / 4) := virasoroHalfCubic_spec.1
  have hs1_eq : s₁_aux = virRsIn / 4 := virasoroHalfCubic_spec.2.1
  have hra_le_poly : r_a_aux ≤ virPoly.r_a := by
    rw [show r_a_aux = min virRaIn ((virRsIn / 2) ^ 2 / 4) from hra_eq]
    exact (min_le_left _ _).trans virRaIn_le_poly
  have hs1_sq : s₁_aux ^ 2 < r_q_aux := by
    rw [show s₁_aux = virRsIn / 4 from hs1_eq]
    dsimp [r_q_aux]
    have h1 : virRsIn ≤ virR0Div / 4 := min_le_left _ _
    have h2 : (virRsIn / 4) ^ 2 ≤ (virR0Div / 16) ^ 2 := by
      have := virRsIn_pos
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [sq_pos_of_pos virR0Div_pos]
  have hB_s : ∀ n, 1 ≤ n → ∀ a ∈ ball (0 : ℂ) virPoly.r_a,
      DifferentiableOn ℂ (fun ζ => virBaux n ζ a) (ball 0 virPoly.r_s) := fun n hn a ha =>
    ((virPoly.hG_s a ha).mul (virPoly.hW_s a ha)).mul (virPoly.hEb_s n hn a ha)
  have hB_a : ∀ n, 1 ≤ n → ∀ ζ ∈ ball (0 : ℂ) virPoly.r_s,
      DifferentiableOn ℂ (virBaux n ζ) (ball 0 virPoly.r_a) := fun n hn ζ hζ =>
    ((virPoly.hG_a ζ hζ).mul (virPoly.hW_a ζ hζ)).mul (virPoly.hEb_a n hn ζ hζ)
  have hB_M : ∀ n, 1 ≤ n → ∀ ζ ∈ sphere (0 : ℂ) virR0Div, ∀ a ∈ ball (0 : ℂ) virPoly.r_a,
      ‖virBaux n ζ a‖ ≤ virMauxBound := fun n hn ζ hζ a ha =>
    virBaux_norm_le hn (by rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ]; exact virR0Div_lt) ha
  let E_aux : ℝ → ℂ → ℂ → ℂ := fun n q a => evenCauchy (virBaux n) virR0Div q a
  let O_aux : ℝ → ℂ → ℂ → ℂ := fun n q a => oddCauchy (virBaux n) virR0Div q a
  have h_ra_lt : ∀ {a : ℂ}, a ∈ ball (0 : ℂ) r_a_aux → a ∈ ball (0 : ℂ) virPoly.r_a := fun ha =>
    mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp ha).trans_le hra_le_poly)
  have hMaux_nn : 0 ≤ virMauxBound := by
    have := virPoly.hMG0; have := virPoly.hKb; unfold virMauxBound; positivity
  let d_aux : HalfCubicData :=
    { r_q := r_q_aux
      r_a := r_a_aux
      s₁ := s₁_aux
      M_E := 2 * virMauxBound
      M_O := (2 / virR0Div) * virMauxBound
      M_ψ := virasoroHalfCubic.M_ψ
      hr_q := by dsimp [r_q_aux]; have := virR0Div_pos; positivity
      hr_a := virasoroHalfCubic.hr_a
      hs₁ := virasoroHalfCubic.hs₁
      hs₁_sq := hs1_sq
      hM_E := by positivity
      hM_O := by have := virR0Div_pos; positivity
      hM_ψ := virasoroHalfCubic.hM_ψ
      E := E_aux
      O := O_aux
      ψ := virasoroHalfCubic.ψ
      hE_q := fun n a hn ha =>
        differentiableOn_evenCauchy_q virR0Div_pos virR0Div_lt (hB_s n hn) (hB_M n hn) (h_ra_lt ha)
      hE_a := fun n q hn hq =>
        (differentiableOn_evenCauchy_a virR0Div_pos virR0Div_lt (hB_s n hn) (hB_a n hn) (hB_M n hn) hq).mono
          (ball_subset_ball hra_le_poly)
      hE_bd := fun n q a hn hq ha =>
        evenCauchy_norm_le' virR0Div_pos hq (fun ζ hζ => hB_M n hn ζ hζ a (h_ra_lt ha))
      hE_real := fun n q a hn hq ha =>
        evenCauchy_real_of_symm virR0Div_pos virR0Div_lt (hB_s n hn) (hB_M n hn)
          (fun x y hx hy => virBaux_symm n hn x y hx hy) hq (ha.trans_le hra_le_poly)
      hO_q := fun n a hn ha =>
        differentiableOn_oddCauchy_q virR0Div_pos virR0Div_lt (hB_s n hn) (hB_M n hn) (h_ra_lt ha)
      hO_a := fun n q hn hq =>
        (differentiableOn_oddCauchy_a virR0Div_pos virR0Div_lt (hB_s n hn) (hB_a n hn) (hB_M n hn) hq).mono
          (ball_subset_ball hra_le_poly)
      hO_bd := fun n q a hn hq ha =>
        oddCauchy_norm_le virR0Div_pos hq (fun ζ hζ => hB_M n hn ζ hζ a (h_ra_lt ha))
      hO_real := fun n q a hn hq ha =>
        oddCauchy_real_of_symm virR0Div_pos virR0Div_lt (hB_s n hn) (hB_M n hn)
          (fun x y hx hy => virBaux_symm n hn x y hx hy) hq (ha.trans_le hra_le_poly)
      hψ_a := virasoroHalfCubic.hψ_a
      hψ_bd := virasoroHalfCubic.hψ_bd
      hψ_real := virasoroHalfCubic.hψ_real }
  refine ⟨d_aux, rfl, rfl, rfl, fun n a s hn ha hs => ?_⟩
  have hlt : virRsIn / 2 < virR0Div := by linarith [virRsIn_lt_virR0Div, virRsIn_pos]
  have hs_r0 : ‖s‖ < virR0Div := hs.trans hlt
  exact evenCauchy_add_oddCauchy virR0Div_pos virR0Div_lt (hB_s n hn a (h_ra_lt ha)) hs_r0

/-- Canonical auxiliary `HalfCubicData` for `virBaux`. -/
def virasoroHalfCubicAux : HalfCubicData := Classical.choose virasoroHalfCubicAux_exists

lemma virasoroHalfCubicAux_spec :
    virasoroHalfCubicAux.r_a = virasoroHalfCubic.r_a ∧
    virasoroHalfCubicAux.s₁ = virasoroHalfCubic.s₁ ∧
    virasoroHalfCubicAux.ψ = virasoroHalfCubic.ψ ∧
    (∀ n a s, 1 ≤ n → a ∈ ball (0 : ℂ) virasoroHalfCubicAux.r_a → ‖s‖ < virRsIn / 2 →
      virasoroHalfCubicAux.B n a s = virBaux n s a) :=
  Classical.choose_spec virasoroHalfCubicAux_exists

/-! ### 3. Coordinate inverse `virPhiInv` and exact matching `uReal c (virPhiInv c x).re = x` -/

/-- Rescaled complex inverse fold chart `aInv_c(z) = 2^{2/3} c^{-2/3} φ_c(z)` mapping
the Airy coordinate `x ∈ [-R, R]` back to the half-cubic parameter `a`. -/
def virPhiInv (c : ℝ) (z : ℂ) : ℂ :=
  (((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * virasoroPhi c z

/-- Exact algebraic match `d.uReal c (virPhiInv c (x : ℂ)).re = x` and polydisc containment
for `virasoroHalfCubic` (hence also for `virasoroHalfCubicAux`, which shares `ψ` and `r_a`). -/
theorem virasoroHalfCubic_uReal_virPhiInv :
    ∃ c_inv cu_max : ℝ, 2 ≤ c_inv ∧ 0 < cu_max ∧ cu_max ≤ virasoroC1 ∧
      ∀ {c R : ℝ}, c_inv ≤ c → 1 ≤ R → R ≤ cu_max * c ^ (2 / 3 : ℝ) →
        ∃ ρ : ℝ, R < ρ ∧
          DifferentiableOn ℂ (virPhiInv c) (ball 0 ρ) ∧
          (∀ z ∈ ball (0 : ℂ) ρ, virPhiInv c z ∈ ball (0 : ℂ) virasoroHalfCubic.rAShrunk) ∧
          (∀ x : ℝ, |x| ≤ R → (virPhiInv c (x : ℂ)).im = 0) ∧
          (∀ x : ℝ, |x| ≤ R → virasoroHalfCubic.uReal c (virPhiInv c (x : ℂ)).re = x) := by
  obtain ⟨cc, C_phi, hC_nn, hspec⟩ := virasoroChart_holds
  have hsh_pos : 0 < virasoroHalfCubic.rAShrunk :=
    lt_min (half_pos virasoroHalfCubic.hr_a) (by have := virasoroHalfCubic.hs₁; positivity)
  let cu_max : ℝ := min (min virasoroC1 (2 * virasoroC1 ^ 2)) (virasoroHalfCubic.rAShrunk / 8)
  have hcu_pos : 0 < cu_max := lt_min (lt_min virasoroC1_pos (by have := virasoroC1_pos; positivity)) (by positivity)
  have hcu_le : cu_max ≤ virasoroC1 := (min_le_left _ _).trans (min_le_left _ _)
  let c_inv : ℝ := max (max 2 cc) (2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (virasoroHalfCubic.rAShrunk / 4) + 1)
  have hc_inv_ge2 : 2 ≤ c_inv := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨c_inv, cu_max, hc_inv_ge2, hcu_pos, hcu_le, ?_⟩
  intro c R hc hR1 hR_le
  have hcc : cc ≤ c := hc.trans' ((le_max_right 2 cc).trans (le_max_left _ _))
  have hc0 : 0 < c := by linarith
  have hc_big : 2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (virasoroHalfCubic.rAShrunk / 4) + 1 ≤ c :=
    hc.trans' (le_max_right _ _)
  obtain ⟨⟨ρ_ch, hρ_ch, hφ_diff⟩, hφ_im, hφ_close, hφ_inv, -⟩ := hspec c hcc
  let ρ : ℝ := min (R + 1) (2 * cu_max * c ^ (2 / 3 : ℝ))
  have hR_lt_2cu : R < 2 * cu_max * c ^ (2 / 3 : ℝ) := by
    have : 0 < cu_max * c ^ (2 / 3 : ℝ) := mul_pos hcu_pos (Real.rpow_pos_of_pos hc0 _)
    linarith
  have hR_lt_ρ : R < ρ := lt_min (by linarith) hR_lt_2cu
  have hρ_le_rmax : ρ ≤ lowerRmax virasoroC1 c := by
    refine (min_le_right _ _).trans ?_
    unfold lowerRmax
    have h2cu : 2 * cu_max ≤ 4 * virasoroC1 ^ 2 := by
      have : cu_max ≤ 2 * virasoroC1 ^ 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith
    exact mul_le_mul_of_nonneg_right h2cu (Real.rpow_nonneg hc0.le _)
  refine ⟨ρ, hR_lt_ρ, ?_, ?_, ?_, ?_⟩
  · exact (hφ_diff.mono (ball_subset_ball (hρ_le_rmax.trans hρ_ch.le))).const_mul _
  · intro z hz
    have hz_norm : ‖z‖ ≤ lowerRmax virasoroC1 c :=
      (mem_ball_zero_iff.mp hz).le.trans hρ_le_rmax
    have hφ_bd := (hφ_close z hz_norm).1
    have htri : ‖virasoroPhi c z‖ ≤ ‖z‖ + C_phi * c ^ (-(1 / 3 : ℝ)) := by
      have h1 := norm_add_le (virasoroPhi c z - z) z
      rw [sub_add_cancel] at h1
      linarith
    have hscale_pos : 0 < (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) := by positivity
    have hpow_mul : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; simp
    have hpow_neg1 : c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) = c⁻¹ := by
      rw [← Real.rpow_add hc0, show -(2 / 3 : ℝ) + -(1 / 3 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have hc_inv_bd : (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * c⁻¹ < virasoroHalfCubic.rAShrunk / 4 := by
      have hc_lt : 2 ^ (2 / 3 : ℝ) * (C_phi + 1) / (virasoroHalfCubic.rAShrunk / 4) < c := by linarith
      rw [div_lt_iff₀ (by positivity)] at hc_lt
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by positivity
      have hlt2 : (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi < (virasoroHalfCubic.rAShrunk / 4) * c := by linarith
      rw [← div_eq_mul_inv]
      exact (div_lt_iff₀ hc0).mpr (by linarith)
    have h2pow_lt : (2 : ℝ) ^ (5 / 3 : ℝ) ≤ 4 := by
      have : (2 : ℝ) ^ (5 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
      norm_num at this; exact this
    have hcu_part : (2 : ℝ) ^ (2 / 3 : ℝ) * (2 * cu_max) ≤ virasoroHalfCubic.rAShrunk / 2 := by
      have h25 : (2 : ℝ) ^ (2 / 3 : ℝ) * 2 = (2 : ℝ) ^ (5 / 3 : ℝ) := by
        conv_lhs => rhs; rw [← Real.rpow_one 2]
        rw [← Real.rpow_add zero_lt_two]; norm_num
      have hcu8 : cu_max ≤ virasoroHalfCubic.rAShrunk / 8 := min_le_right _ _
      calc (2 : ℝ) ^ (2 / 3 : ℝ) * (2 * cu_max)
          = (2 : ℝ) ^ (5 / 3 : ℝ) * cu_max := by rw [← mul_assoc, h25]
        _ ≤ 4 * (virasoroHalfCubic.rAShrunk / 8) := mul_le_mul h2pow_lt hcu8 hcu_pos.le (by norm_num)
        _ = virasoroHalfCubic.rAShrunk / 2 := by ring
    have hz_2cu : ‖z‖ + C_phi * c ^ (-(1 / 3 : ℝ)) ≤ 2 * cu_max * c ^ (2 / 3 : ℝ) + C_phi * c ^ (-(1 / 3 : ℝ)) :=
      by linarith [(mem_ball_zero_iff.mp hz).le.trans (min_le_right (R + 1) (2 * cu_max * c ^ (2 / 3 : ℝ)))]
    rw [mem_ball_zero_iff]
    unfold virPhiInv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale_pos]
    calc ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) * ‖virasoroPhi c z‖
        ≤ ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ))) *
            (2 * cu_max * c ^ (2 / 3 : ℝ) + C_phi * c ^ (-(1 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left (htri.trans hz_2cu) hscale_pos.le
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (2 * cu_max) * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) +
            (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * (c ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) := by ring
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) * (2 * cu_max) + (2 : ℝ) ^ (2 / 3 : ℝ) * C_phi * c⁻¹ := by
          rw [hpow_mul, hpow_neg1, mul_one]
      _ < virasoroHalfCubic.rAShrunk / 2 + virasoroHalfCubic.rAShrunk / 4 := by linarith
      _ < virasoroHalfCubic.rAShrunk := by linarith [hsh_pos]
  · intro x hx
    have hx_rmax : |x| ≤ lowerRmax virasoroC1 c := hx.trans (hR_lt_ρ.le.trans hρ_le_rmax)
    unfold virPhiInv
    rw [Complex.im_ofReal_mul, hφ_im x hx_rmax, mul_zero]
  · intro x hx
    have hx_rmax : |x| ≤ lowerRmax virasoroC1 c := hx.trans (hR_lt_ρ.le.trans hρ_le_rmax)
    set u : ℝ := (virasoroPhi c (x : ℂ)).re
    have hre : (virPhiInv c (x : ℂ)).re = (2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * u := by
      unfold virPhiInv; rw [Complex.re_ofReal_mul]
    unfold HalfCubicData.uReal HalfCubicData.aHat
    rw [virasoroHalfCubic_spec.2.2.2.1]
    have hu_pos_mul : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) *
        ((virPhiInv c (x : ℂ)).re + c⁻¹ * (virPsi c ((virPhiInv c (x : ℂ)).re : ℂ)).re) =
        virasoroUhat c u := by
      rw [hre]
      have hψ_eq : (virPsi c (((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * u : ℝ) : ℂ)).re =
          ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip) *
            (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * u : ℝ) : ℂ)).re := by
        unfold virPsi
        have harg : ((((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip)⁻¹ : ℝ) : ℂ) *
            (((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * u : ℝ) : ℂ) =
            ((virasoroMu c * u : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]; congr 1
          unfold virasoroMu; field_simp [betaTip_pos.ne']
        rw [harg, Complex.re_ofReal_mul]
      have h2c : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add zero_lt_two]; simp
      have hcc_1 : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
        rw [← Real.rpow_add hc0]; simp
      have hcc_lam : c ^ (2 / 3 : ℝ) * c⁻¹ = c ^ (-(1 / 3 : ℝ)) := by
        rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
      unfold virasoroUhat fjUhat virasoroPsiChart virasoroLam
      rw [hψ_eq]
      calc (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) *
              ((2 : ℝ) ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) * u +
                c⁻¹ * ((2 : ℝ) ^ (2 / 3 : ℝ) * betaTip *
                  (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * u : ℝ) : ℂ)).re))
          = ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) * (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * u +
              ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (2 / 3 : ℝ)) * betaTip * (c ^ (2 / 3 : ℝ) * c⁻¹) *
                (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * u : ℝ) : ℂ)).re := by ring
        _ = u + betaTip * c ^ (-(1 / 3 : ℝ)) *
              (virasoroPsiEps (c ^ (-2 : ℝ)) ((virasoroMu c * u : ℝ) : ℂ)).re := by
            rw [h2c, hcc_1, hcc_lam]; ring
    have hre_inner : (((virPhiInv c (x : ℂ)).re : ℂ) +
        ((c : ℂ))⁻¹ * virPsi c ((virPhiInv c (x : ℂ)).re : ℂ)).re =
        (virPhiInv c (x : ℂ)).re + c⁻¹ * (virPsi c ((virPhiInv c (x : ℂ)).re : ℂ)).re := by
      simp [Complex.add_re, ← Complex.ofReal_inv]
    rw [hre_inner, hu_pos_mul]
    exact hφ_inv x hx_rmax

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroHalfCubic_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroHalfCubic_exists

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroHalfCubicAux_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroHalfCubicAux_exists

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.virasoroHalfCubic_uReal_virPhiInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms virasoroHalfCubic_uReal_virPhiInv

end
end FormalResearch.ModularBootstrap.FiveTerm
