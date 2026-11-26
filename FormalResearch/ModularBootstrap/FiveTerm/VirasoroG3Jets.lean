module

public import FormalResearch.ModularBootstrap.FiveTerm.Constants
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Cubic jets of real functions (FIVE-0, `ctu:jets`, `g₃`, step 3)

`Jet l f c₀ c₁ c₂ c₃` says `f(x) = c₀ + c₁x + c₂x² + c₃x³ + o(x³)` along the filter `l ≤ 𝓝 0`.  A small calculus
(sum, scalar multiple, composition, the jet of an antiderivative from a second-order jet of the derivative) and the jets
of the elementary functions entering the third odd jet of the Virasoro outer function: `arccos`, `arctan`,
`log(c+w)`, `arsinh√(1-y²)`, and `m(x) = 2√2 x/(1+x²)`.  The coefficients are unique along `𝓝[>] 0` (`Jet.unique`).
Proved.
-/

@[expose] public section

open Filter Topology Asymptotics Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `f(x) = c₀ + c₁x + c₂x² + c₃x³ + o(x³)` along `l`. -/
def Jet (l : Filter ℝ) (f : ℝ → ℝ) (c0 c1 c2 c3 : ℝ) : Prop :=
  (fun x => f x - (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3)) =o[l] fun x => x ^ 3

/-- `f(x) = c₀ + c₁x + c₂x² + o(x²)` along `l`. -/
def Jet2 (l : Filter ℝ) (f : ℝ → ℝ) (c0 c1 c2 : ℝ) : Prop :=
  (fun x => f x - (c0 + c1 * x + c2 * x ^ 2)) =o[l] fun x => x ^ 2

section basic

variable {l : Filter ℝ} {f g : ℝ → ℝ}

lemma Jet.mono {l' : Filter ℝ} (h : l' ≤ l) {c0 c1 c2 c3 : ℝ} (hf : Jet l f c0 c1 c2 c3) :
    Jet l' f c0 c1 c2 c3 := IsLittleO.mono hf h

lemma Jet.congr {c0 c1 c2 c3 : ℝ} (hf : Jet l f c0 c1 c2 c3) (h : ∀ x, f x = g x) : Jet l g c0 c1 c2 c3 := by
  have : f = g := funext h
  rwa [← this]

lemma Jet.add {a0 a1 a2 a3 b0 b1 b2 b3 : ℝ} (hf : Jet l f a0 a1 a2 a3) (hg : Jet l g b0 b1 b2 b3) :
    Jet l (fun x => f x + g x) (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) :=
  (IsLittleO.add hf hg).congr_left (fun x => by ring)

lemma Jet.const_mul (k : ℝ) {a0 a1 a2 a3 : ℝ} (hf : Jet l f a0 a1 a2 a3) :
    Jet l (fun x => k * f x) (k * a0) (k * a1) (k * a2) (k * a3) :=
  (IsLittleO.const_mul_left hf k).congr_left (fun x => by ring)

lemma Jet.neg {a0 a1 a2 a3 : ℝ} (hf : Jet l f a0 a1 a2 a3) :
    Jet l (fun x => -f x) (-a0) (-a1) (-a2) (-a3) :=
  (IsLittleO.neg_left hf).congr_left (fun x => by ring)

lemma Jet.sub {a0 a1 a2 a3 b0 b1 b2 b3 : ℝ} (hf : Jet l f a0 a1 a2 a3) (hg : Jet l g b0 b1 b2 b3) :
    Jet l (fun x => f x - g x) (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) :=
  (IsLittleO.sub hf hg).congr_left (fun x => by ring)

lemma Jet.const (c : ℝ) : Jet l (fun _ => c) c 0 0 0 := by
  unfold Jet
  refine (isLittleO_zero _ _).congr_left (fun x => by ring)

lemma Jet.id (c1 : ℝ) : Jet l (fun x => c1 * x) 0 c1 0 0 := by
  unfold Jet
  refine (isLittleO_zero _ _).congr_left (fun x => by ring)

lemma eventually_abs_lt (hl : l ≤ 𝓝 0) {r : ℝ} (hr : 0 < r) : ∀ᶠ x in l, |x| < r := by
  have : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < r := by
    have := Metric.ball_mem_nhds (0 : ℝ) hr
    filter_upwards [this] with x hx using by simpa using hx
  exact this.filter_mono hl

lemma isLittleO_pow_succ (hl : l ≤ 𝓝 0) (k : ℕ) : (fun x : ℝ => x ^ (k + 1)) =o[l] (fun x => x ^ k) := by
  have h1 : (fun x : ℝ => x) =o[l] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (tendsto_id.mono_left hl)
  exact (h1.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ k) l)).congr (fun x => by ring) (fun x => by ring)

lemma Jet.of_bound (hl : l ≤ 𝓝 0) {c0 c1 c2 c3 K : ℝ}
    (h : ∀ᶠ x in l, |f x - (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3)| ≤ K * |x| ^ 4) :
    Jet l f c0 c1 c2 c3 := by
  have h1 : (fun x => f x - (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3)) =O[l] (fun x : ℝ => x ^ 4) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]; exact hx
  exact h1.trans_isLittleO (isLittleO_pow_succ hl 3)

lemma Jet2.of_bound (hl : l ≤ 𝓝 0) {c0 c1 c2 K : ℝ}
    (h : ∀ᶠ x in l, |f x - (c0 + c1 * x + c2 * x ^ 2)| ≤ K * |x| ^ 3) : Jet2 l f c0 c1 c2 := by
  have h1 : (fun x => f x - (c0 + c1 * x + c2 * x ^ 2)) =O[l] (fun x : ℝ => x ^ 3) := by
    refine IsBigO.of_bound K ?_
    filter_upwards [h] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]; exact hx
  exact h1.trans_isLittleO (isLittleO_pow_succ hl 2)

lemma Jet.tendsto_zero (hl : l ≤ 𝓝 0) {g1 g2 g3 : ℝ} (hg : Jet l g 0 g1 g2 g3) : Tendsto g l (𝓝 0) := by
  have h3 : Tendsto (fun x : ℝ => x ^ 3) l (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x ^ 3) (𝓝 0) (𝓝 (0 ^ 3)) := (continuous_pow 3).tendsto 0
    simpa using this.mono_left hl
  have h1 : Tendsto (fun x => g x - (0 + g1 * x + g2 * x ^ 2 + g3 * x ^ 3)) l (𝓝 0) :=
    hg.isBigO.trans_tendsto h3
  have h2 : Tendsto (fun x : ℝ => 0 + g1 * x + g2 * x ^ 2 + g3 * x ^ 3) l (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 0 + g1 * x + g2 * x ^ 2 + g3 * x ^ 3) (𝓝 0)
        (𝓝 (0 + g1 * 0 + g2 * 0 ^ 2 + g3 * 0 ^ 3)) := by
      have : Continuous (fun x : ℝ => 0 + g1 * x + g2 * x ^ 2 + g3 * x ^ 3) := by fun_prop
      exact this.tendsto 0
    simpa using this.mono_left hl
  simpa using h1.add h2

end basic

/-! ### The mean-value step -/

lemma mvt_littleO {g g' : ℝ → ℝ} (k : ℕ) (hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt g (g' x) x) (h0 : g 0 = 0)
    (hg' : g' =o[𝓝 0] fun x => x ^ k) : g =o[𝓝 0] fun x => x ^ (k + 1) := by
  rw [isLittleO_iff]
  intro c hc
  have h1 := hg'.def hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hd.and h1)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with x hx
  have hxδ : |x| < δ := by simpa using hx
  have hmem : ∀ ξ ∈ Metric.closedBall (0 : ℝ) |x|, ξ ∈ Metric.ball (0 : ℝ) δ := by
    intro ξ hξ
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hξ
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith
  have hbound := (convex_closedBall (0 : ℝ) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (C := c * |x| ^ k) (x := 0) (y := x)
    (fun ξ hξ => (hball (hmem ξ hξ)).1.hasDerivWithinAt)
    (fun ξ hξ => by
      have := (hball (hmem ξ hξ)).2
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at this
      have hξ' : |ξ| ≤ |x| := by
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hξ; exact hξ
      calc ‖g' ξ‖ ≤ c * |ξ| ^ k := by rw [Real.norm_eq_abs]; exact this
        _ ≤ c * |x| ^ k := by gcongr)
    (Metric.mem_closedBall_self (abs_nonneg x))
    (by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs])
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  calc ‖g x‖ ≤ c * |x| ^ k * |x| := hbound
    _ = c * |x| ^ (k + 1) := by ring

lemma Jet.of_deriv {f f' : ℝ → ℝ} {b0 b1 b2 : ℝ} (hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (f' x) x)
    (hj : Jet2 (𝓝 0) f' b0 b1 b2) : Jet (𝓝 0) f (f 0) b0 (b1 / 2) (b2 / 3) := by
  have hd' : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun x => f x - (f 0 + b0 * x + b1 / 2 * x ^ 2 + b2 / 3 * x ^ 3))
      (f' x - (b0 + b1 * x + b2 * x ^ 2)) x := by
    filter_upwards [hd] with x hx
    have hp : HasDerivAt (fun x : ℝ => f 0 + b0 * x + b1 / 2 * x ^ 2 + b2 / 3 * x ^ 3)
        (b0 + b1 * x + b2 * x ^ 2) x := by
      have h1 : HasDerivAt (fun x : ℝ => b0 * x) b0 x := by simpa using (hasDerivAt_id x).const_mul b0
      have h2 : HasDerivAt (fun x : ℝ => b1 / 2 * x ^ 2) (b1 * x) x :=
        ((hasDerivAt_pow 2 x).const_mul (b1 / 2)).congr_deriv (by simp; ring)
      have h3 : HasDerivAt (fun x : ℝ => b2 / 3 * x ^ 3) (b2 * x ^ 2) x :=
        ((hasDerivAt_pow 3 x).const_mul (b2 / 3)).congr_deriv (by simp; ring)
      have := (((hasDerivAt_const x (f 0)).fun_add h1).fun_add h2).fun_add h3
      simpa using this
    exact hx.sub hp
  have := mvt_littleO 2 hd' (by simp) hj
  unfold Jet
  simpa using this

lemma Jet2.of_deriv {f f' : ℝ → ℝ} {b0 b1 : ℝ} (hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt f (f' x) x)
    (hj : (fun x => f' x - (b0 + b1 * x)) =o[𝓝 0] fun x => x) : Jet2 (𝓝 0) f (f 0) b0 (b1 / 2) := by
  have hd' : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (fun x => f x - (f 0 + b0 * x + b1 / 2 * x ^ 2))
      (f' x - (b0 + b1 * x)) x := by
    filter_upwards [hd] with x hx
    have hp : HasDerivAt (fun x : ℝ => f 0 + b0 * x + b1 / 2 * x ^ 2) (b0 + b1 * x) x := by
      have h1 : HasDerivAt (fun x : ℝ => b0 * x) b0 x := by simpa using (hasDerivAt_id x).const_mul b0
      have h2 : HasDerivAt (fun x : ℝ => b1 / 2 * x ^ 2) (b1 * x) x :=
        ((hasDerivAt_pow 2 x).const_mul (b1 / 2)).congr_deriv (by simp; ring)
      have := ((hasDerivAt_const x (f 0)).fun_add h1).fun_add h2
      simpa using this
    exact hx.sub hp
  have := mvt_littleO 1 hd' (by simp) (by simpa using hj)
  unfold Jet2
  simpa using this

/-! ### Composition -/

lemma isBigO_one_of_continuous {l : Filter ℝ} (hl : l ≤ 𝓝 0) {p : ℝ → ℝ} (hp : Continuous p) :
    p =O[l] (fun _ => (1 : ℝ)) :=
  ((hp.tendsto 0).mono_left hl).isBigO_one ℝ

lemma Jet.comp {l l' : Filter ℝ} (hl : l ≤ 𝓝 0) {f g : ℝ → ℝ} {f0 f1 f2 f3 g1 g2 g3 : ℝ}
    (hf : Jet l' f f0 f1 f2 f3) (hg : Jet l g 0 g1 g2 g3) (ht : Tendsto g l l') :
    Jet l (fun x => f (g x)) f0 (f1 * g1) (f1 * g2 + f2 * g1 ^ 2)
      (f1 * g3 + 2 * f2 * g1 * g2 + f3 * g1 ^ 3) := by
  have hg0 : Tendsto g l (𝓝 0) := hg.tendsto_zero hl
  have hA : (fun x => (f (g x) - (f0 + f1 * g x + f2 * g x ^ 2 + f3 * g x ^ 3))) =o[l] fun x => g x ^ 3 :=
    hf.comp_tendsto ht
  set Tg : ℝ → ℝ := fun x => g1 * x + g2 * x ^ 2 + g3 * x ^ 3 with hTg
  set rg : ℝ → ℝ := fun x => g x - Tg x with hrg
  have hrgo : rg =o[l] fun x : ℝ => x ^ 3 := by
    refine hg.congr_left (fun x => ?_)
    simp only [hrg, hTg]; ring
  have hx3 : (fun x : ℝ => x ^ 3) =O[l] (fun x : ℝ => x) := by
    have h1 : (fun x : ℝ => x ^ 2) =O[l] (fun _ => (1 : ℝ)) := isBigO_one_of_continuous hl (by fun_prop)
    exact ((isBigO_refl (fun x : ℝ => x) l).mul h1).congr (fun x => by ring) (fun x => by ring)
  have hTgO : Tg =O[l] fun x : ℝ => x := by
    have ht1 : (fun x : ℝ => g1 + g2 * x + g3 * x ^ 2) =O[l] (fun _ => (1 : ℝ)) :=
      isBigO_one_of_continuous hl (by fun_prop)
    exact ((isBigO_refl (fun x : ℝ => x) l).mul ht1).congr (fun x => by simp only [hTg]; ring)
      (fun x => by ring)
  have hgO : g =O[l] fun x : ℝ => x := by
    have : g = fun x => Tg x + rg x := by funext x; simp only [hrg]; ring
    rw [this]
    exact hTgO.add (hrgo.isBigO.trans hx3)
  have hg3O : (fun x => g x ^ 3) =O[l] fun x : ℝ => x ^ 3 := hgO.pow 3
  have hAo : (fun x => (f (g x) - (f0 + f1 * g x + f2 * g x ^ 2 + f3 * g x ^ 3))) =o[l] fun x : ℝ => x ^ 3 :=
    hA.trans_isBigO hg3O
  have hTg0 : Tendsto Tg l (𝓝 0) := by
    have : Tendsto Tg (𝓝 0) (𝓝 (Tg 0)) := by
      have : Continuous Tg := by simp only [hTg]; fun_prop
      exact this.tendsto 0
    simpa [hTg] using this.mono_left hl
  have hBd : (fun x => f1 + f2 * (g x + Tg x) + f3 * (g x ^ 2 + g x * Tg x + Tg x ^ 2)) =O[l]
      (fun _ => (1 : ℝ)) := by
    have : Tendsto (fun x => f1 + f2 * (g x + Tg x) + f3 * (g x ^ 2 + g x * Tg x + Tg x ^ 2)) l
        (𝓝 (f1 + f2 * (0 + 0) + f3 * (0 ^ 2 + 0 * 0 + 0 ^ 2))) :=
      (tendsto_const_nhds.add ((hg0.add hTg0).const_mul f2)).add
        ((((hg0.pow 2).add (hg0.mul hTg0)).add (hTg0.pow 2)).const_mul f3)
    exact this.isBigO_one ℝ
  have hmid : (fun x => rg x * (f1 + f2 * (g x + Tg x) + f3 * (g x ^ 2 + g x * Tg x + Tg x ^ 2))) =o[l]
      fun x : ℝ => x ^ 3 :=
    (hrgo.mul_isBigO hBd).congr_right (fun x => by ring)
  set R : ℝ → ℝ := fun x => f2 * ((g2 ^ 2 + 2 * g1 * g3) + 2 * g2 * g3 * x + g3 ^ 2 * x ^ 2) +
    f3 * (g2 + g3 * x) * ((g1 + g2 * x + g3 * x ^ 2) ^ 2 + (g1 + g2 * x + g3 * x ^ 2) * g1 + g1 ^ 2) with hR
  have hRO : R =O[l] (fun _ => (1 : ℝ)) := isBigO_one_of_continuous hl (by simp only [hR]; fun_prop)
  have hlast : (fun x => x ^ 4 * R x) =o[l] fun x : ℝ => x ^ 3 :=
    ((isLittleO_pow_succ hl 3).mul_isBigO hRO).congr (fun x => by ring) (fun x => by ring)
  unfold Jet
  refine ((hAo.add hmid).add hlast).congr_left (fun x => ?_)
  simp only [hrg, hTg, hR]
  ring

/-! ### Uniqueness of the coefficients -/

lemma tendsto_div_pow_of_littleO {Q : ℝ → ℝ} (hQ : Q =o[𝓝[>] 0] fun x : ℝ => x ^ 3) {k : ℕ} (hk : k ≤ 3) :
    Tendsto (fun x => Q x / x ^ k) (𝓝[>] 0) (𝓝 0) := by
  have h1 : (fun x : ℝ => x ^ 3) =O[𝓝[>] 0] (fun x : ℝ => x ^ k) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_abs_lt (l := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds one_pos] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, one_mul]
    exact pow_le_pow_of_le_one (abs_nonneg x) hx.le hk
  have h2 : Q =o[𝓝[>] 0] fun x : ℝ => x ^ k := hQ.trans_isBigO h1
  refine h2.tendsto_div_nhds_zero

lemma Jet.unique {f : ℝ → ℝ} {c0 c1 c2 c3 d0 d1 d2 d3 : ℝ}
    (hc : Jet (𝓝[>] 0) f c0 c1 c2 c3) (hd : Jet (𝓝[>] 0) f d0 d1 d2 d3) :
    c0 = d0 ∧ c1 = d1 ∧ c2 = d2 ∧ c3 = d3 := by
  have hQ : (fun x => (c0 - d0) + (c1 - d1) * x + (c2 - d2) * x ^ 2 + (c3 - d3) * x ^ 3) =o[𝓝[>] 0]
      fun x : ℝ => x ^ 3 :=
    (hd.sub hc).congr_left (fun x => by ring)
  set Q : ℝ → ℝ := fun x => (c0 - d0) + (c1 - d1) * x + (c2 - d2) * x ^ 2 + (c3 - d3) * x ^ 3 with hQdef
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  -- k = 0
  have t0 : Tendsto Q (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_div_pow_of_littleO hQ (k := 0) (by norm_num)
  have l0 : Tendsto Q (𝓝[>] 0) (𝓝 (c0 - d0)) := by
    have : Tendsto Q (𝓝 0) (𝓝 (Q 0)) := by
      have : Continuous Q := by simp only [hQdef]; fun_prop
      exact this.tendsto 0
    simpa [hQdef] using this.mono_left nhdsWithin_le_nhds
  have e0 : c0 - d0 = 0 := tendsto_nhds_unique l0 t0
  -- k = 1
  have t1 := tendsto_div_pow_of_littleO hQ (k := 1) (by norm_num)
  have l1 : Tendsto (fun x => Q x / x ^ 1) (𝓝[>] 0) (𝓝 (c1 - d1)) := by
    have h : Tendsto (fun x : ℝ => (c1 - d1) + (c2 - d2) * x + (c3 - d3) * x ^ 2) (𝓝 0)
        (𝓝 ((c1 - d1) + (c2 - d2) * 0 + (c3 - d3) * 0 ^ 2)) := by
      have : Continuous (fun x : ℝ => (c1 - d1) + (c2 - d2) * x + (c3 - d3) * x ^ 2) := by fun_prop
      exact this.tendsto 0
    simp only [mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hpos] with x hx
    simp only [hQdef, e0]; field_simp; ring
  have e1 : c1 - d1 = 0 := tendsto_nhds_unique l1 t1
  -- k = 2
  have t2 := tendsto_div_pow_of_littleO hQ (k := 2) (by norm_num)
  have l2 : Tendsto (fun x => Q x / x ^ 2) (𝓝[>] 0) (𝓝 (c2 - d2)) := by
    have h : Tendsto (fun x : ℝ => (c2 - d2) + (c3 - d3) * x) (𝓝 0) (𝓝 ((c2 - d2) + (c3 - d3) * 0)) := by
      have : Continuous (fun x : ℝ => (c2 - d2) + (c3 - d3) * x) := by fun_prop
      exact this.tendsto 0
    simp only [mul_zero, add_zero] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hpos] with x hx
    simp only [hQdef, e0, e1]; field_simp; ring
  have e2 : c2 - d2 = 0 := tendsto_nhds_unique l2 t2
  -- k = 3
  have t3 := tendsto_div_pow_of_littleO hQ (k := 3) (by norm_num)
  have l3 : Tendsto (fun x => Q x / x ^ 3) (𝓝[>] 0) (𝓝 (c3 - d3)) := by
    refine (tendsto_const_nhds (x := c3 - d3)).congr' ?_
    filter_upwards [hpos] with x hx
    simp only [hQdef, e0, e1, e2]; field_simp; ring
  have e3 : c3 - d3 = 0 := tendsto_nhds_unique l3 t3
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma Jet.of_eq {l : Filter ℝ} {f : ℝ → ℝ} {c0 c1 c2 c3 c0' c1' c2' c3' : ℝ} (h : Jet l f c0 c1 c2 c3)
    (e0 : c0 = c0') (e1 : c1 = c1') (e2 : c2 = c2') (e3 : c3 = c3') : Jet l f c0' c1' c2' c3' := by
  subst e0 e1 e2 e3; exact h

/-! ### Elementary jets -/

lemma jet_arctan : Jet (𝓝 0) Real.arctan 0 1 0 (-1 / 3) := by
  have hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
    Eventually.of_forall fun x => Real.hasDerivAt_arctan x
  have hj : Jet2 (𝓝 0) (fun x => 1 / (1 + x ^ 2)) 1 0 (-1) := by
    refine Jet2.of_bound (K := 1) le_rfl ?_
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl one_pos] with x hx
    have h1 : 1 / (1 + x ^ 2) - (1 + 0 * x + (-1) * x ^ 2) = x ^ 4 / (1 + x ^ 2) := by
      field_simp; ring
    rw [h1, abs_of_nonneg (by positivity)]
    have h2 : x ^ 4 = |x| ^ 4 := ((show Even 4 by decide).pow_abs x).symm
    calc x ^ 4 / (1 + x ^ 2) ≤ x ^ 4 := div_le_self (by positivity) (by nlinarith [sq_nonneg x])
      _ = |x| ^ 4 := h2
      _ ≤ |x| ^ 3 := pow_le_pow_of_le_one (abs_nonneg x) hx.le (by norm_num)
      _ = 1 * |x| ^ 3 := (one_mul _).symm
  have := Jet.of_deriv hd hj
  exact this.of_eq (by simp) rfl (by simp) rfl

lemma jet_log_add {c : ℝ} (hc : 0 < c) :
    Jet (𝓝 0) (fun w => Real.log (c + w)) (Real.log c) (1 / c) (-1 / (2 * c ^ 2)) (1 / (3 * c ^ 3)) := by
  have hd : ∀ᶠ w in 𝓝 (0 : ℝ), HasDerivAt (fun w => Real.log (c + w)) (1 / (c + w)) w := by
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl hc] with w hw
    have hne : c + w ≠ 0 := by
      have := abs_lt.mp hw; intro h; linarith [this.1]
    have := ((hasDerivAt_id w).const_add c).log hne
    simpa using this
  have hj : Jet2 (𝓝 0) (fun w => 1 / (c + w)) (1 / c) (-1 / c ^ 2) (1 / c ^ 3) := by
    refine Jet2.of_bound (K := 2 / c ^ 4) le_rfl ?_
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl (half_pos hc)] with w hw
    have hw' := abs_lt.mp hw
    have hpos : 0 < c + w := by linarith [hw'.1]
    have h1 : 1 / (c + w) - (1 / c + (-1 / c ^ 2) * w + (1 / c ^ 3) * w ^ 2) = -w ^ 3 / (c ^ 3 * (c + w)) := by
      field_simp; ring
    rw [h1, abs_div, abs_neg, abs_pow, abs_of_pos (mul_pos (pow_pos hc 3) hpos),
      div_le_iff₀ (mul_pos (pow_pos hc 3) hpos)]
    have key : 1 ≤ 2 / c ^ 4 * (c ^ 3 * (c + w)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc 4)]
      nlinarith [pow_pos hc 3, hw'.1]
    calc |w| ^ 3 = |w| ^ 3 * 1 := (mul_one _).symm
      _ ≤ |w| ^ 3 * (2 / c ^ 4 * (c ^ 3 * (c + w))) := by gcongr
      _ = 2 / c ^ 4 * |w| ^ 3 * (c ^ 3 * (c + w)) := by ring
  have := Jet.of_deriv hd hj
  refine this.of_eq (by simp) rfl ?_ ?_ <;> (field_simp)

lemma jet_arccos : Jet (𝓝 0) Real.arccos (π / 2) (-1) 0 (-1 / 6) := by
  have hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt Real.arccos (-(1 / √(1 - x ^ 2))) x := by
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl one_pos] with x hx
    have hx' := abs_lt.mp hx
    exact Real.hasDerivAt_arccos (by intro h; linarith [hx'.1]) (by intro h; linarith [hx'.2])
  have hq : HasDerivAt (fun u : ℝ => (√(1 - u))⁻¹) (1 / 2) 0 := by
    have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have h2 := (h1.sqrt (by norm_num)).inv (by simp)
    convert h2 using 1
    norm_num
  have hqo := hq.isLittleO
  have hu : Tendsto (fun y : ℝ => y ^ 2) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => y ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
    simpa using this
  have hcomp := hqo.comp_tendsto hu
  have hj : Jet2 (𝓝 0) (fun x => -(1 / √(1 - x ^ 2))) (-1) 0 (-1 / 2) := by
    unfold Jet2
    have := hcomp.neg_left
    refine this.congr (fun y => ?_) (fun y => ?_)
    · simp [one_div]; ring
    · simp
  have := Jet.of_deriv hd hj
  exact this.of_eq (by simp) rfl (by simp) (by norm_num)

/-- `φ(y) = arsinh √(1 - y²)`. -/
noncomputable def phiR (y : ℝ) : ℝ := Real.arsinh (√(1 - y ^ 2))

lemma jet_phi : Jet (𝓝 0) phiR (Real.arsinh 1) 0 (-(1 / (2 * √2))) 0 := by
  set κ : ℝ → ℝ := fun y => 1 / (√(1 - y ^ 2) * √(2 - y ^ 2)) with hκ
  have hd : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt phiR (-(x * κ x)) x := by
    filter_upwards [eventually_abs_lt (l := 𝓝 (0 : ℝ)) le_rfl one_pos] with x hx
    have hx' := abs_lt.mp hx
    have hpos : 0 < 1 - x ^ 2 := by nlinarith
    have h1 := (((hasDerivAt_pow 2 x).const_sub 1).sqrt hpos.ne').arsinh
    unfold phiR
    refine h1.congr_deriv ?_
    have hs : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hpos.le
    have hs0 : 0 < √(1 - x ^ 2) := Real.sqrt_pos.mpr hpos
    have h2 : (1 : ℝ) + √(1 - x ^ 2) ^ 2 = 2 - x ^ 2 := by rw [hs]; ring
    have hp2 : 0 < 2 - x ^ 2 := by nlinarith
    have hs2 : 0 < √(2 - x ^ 2) := Real.sqrt_pos.mpr hp2
    simp only [hκ]
    rw [h2]
    have hs1 := hs0.ne'
    have hs2' := hs2.ne'
    simp only [Nat.cast_ofNat, smul_eq_mul]
    field_simp
    ring_nf
  have hκd : HasDerivAt κ 0 0 := by
    have h1 : HasDerivAt (fun y : ℝ => √(1 - y ^ 2)) 0 0 := by
      have := ((hasDerivAt_pow 2 (0 : ℝ)).const_sub 1).sqrt (by norm_num)
      simpa using this
    have h2 : HasDerivAt (fun y : ℝ => √(2 - y ^ 2)) 0 0 := by
      have := ((hasDerivAt_pow 2 (0 : ℝ)).const_sub 2).sqrt (by norm_num)
      simpa using this
    have h3 := (h1.mul h2).inv (by simp)
    convert h3 using 1
    · funext y; simp [hκ]
    · simp
  have hκo := hκd.isLittleO
  have hj : Jet2 (𝓝 0) (fun x => -(x * κ x)) 0 (-κ 0) 0 := by
    unfold Jet2
    have h1 : (fun y : ℝ => y * (κ y - κ 0 - (y - 0) • (0 : ℝ))) =o[𝓝 0] fun y : ℝ => y * (y - 0) :=
      (isBigO_refl (fun y : ℝ => y) (𝓝 0)).mul_isLittleO hκo
    refine h1.neg_left.congr (fun y => ?_) (fun y => ?_)
    · simp; ring
    · simp; ring
  have := Jet.of_deriv hd hj
  refine this.of_eq (by simp [phiR]) rfl ?_ (by simp)
  simp only [hκ]
  simp
  ring

/-- `m(x) = 2√2 x/(1+x²)`. -/
noncomputable def mR (x : ℝ) : ℝ := 2 * √2 * x / (1 + x ^ 2)

lemma jet_mR {l : Filter ℝ} (hl : l ≤ 𝓝 0) : Jet l mR 0 (2 * √2) 0 (-(2 * √2)) := by
  refine Jet.of_bound hl (K := 2 * √2) ?_
  filter_upwards [eventually_abs_lt hl one_pos] with x hx
  have h1 : mR x - (0 + 2 * √2 * x + 0 * x ^ 2 + (-(2 * √2)) * x ^ 3) = 2 * √2 * x ^ 5 / (1 + x ^ 2) := by
    unfold mR; field_simp; ring
  rw [h1]
  have h2 : (0 : ℝ) < √2 := by positivity
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos h2]
  have hx1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have h3 : |x| ^ 5 ≤ |x| ^ 4 := pow_le_pow_of_le_one (abs_nonneg x) hx.le (by norm_num)
  calc 2 * √2 * |x| ^ 5 / (1 + x ^ 2) ≤ 2 * √2 * |x| ^ 5 := div_le_self (by positivity) hx1
    _ ≤ 2 * √2 * |x| ^ 4 := by gcongr

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.Jet.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.Jet.comp

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.Jet.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.Jet.unique

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.jet_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.jet_phi

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.jet_arccos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.jet_arccos
