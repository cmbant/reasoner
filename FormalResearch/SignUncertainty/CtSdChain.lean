module

public import FormalResearch.SignUncertainty.CtSdPhase

/-!
# Three-piece polygonal chains from `0` to `p = R e^{iπ/6}` (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3 (`Γ_SD`).  **Proved.**
A `Chain3` is three line pieces (possibly of length zero) joining `0` to `p` inside `B(0,R₀) ∩ {Re ≥ 0}`.  The fundamental theorem of
calculus and the `s^{1/2}g(s)` path independence telescope along it.  Concrete chains: the ray (`U ≥ -1`), and
`0 → v(1-i)/2 → (1+√3)v e^{iπ/6} → p` for `U = -v²/κ`, `v ≥ 1`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

/-- A line piece `t ↦ z₀ + t d`, `t ∈ [a,b]`. -/
abbrev Piece := ℂ × ℂ × ℝ × ℝ

def Piece.z0 (q : Piece) : ℂ := q.1
def Piece.d (q : Piece) : ℂ := q.2.1
def Piece.a (q : Piece) : ℝ := q.2.2.1
def Piece.b (q : Piece) : ℝ := q.2.2.2
def Piece.start (q : Piece) : ℂ := q.z0 + (q.a : ℂ) * q.d
def Piece.stop (q : Piece) : ℂ := q.z0 + (q.b : ℂ) * q.d

/-- Validity of one piece inside `B(0,R₀) ∩ {Re ≥ 0}`, avoiding `0` after its start. -/
def Piece.Ok (R₀ : ℝ) (q : Piece) : Prop :=
  q.a ≤ q.b ∧ (∀ t ∈ Icc q.a q.b, q.z0 + (t : ℂ) * q.d ∈ ball (0 : ℂ) R₀ ∧ 0 ≤ (q.z0 + (t : ℂ) * q.d).re) ∧
    ∀ t ∈ Ioc q.a q.b, q.z0 + (t : ℂ) * q.d ≠ 0

/-- Three consecutive pieces from `0` to `p`. -/
structure Chain3 (R₀ : ℝ) (p : ℂ) where
  q1 : Piece
  q2 : Piece
  q3 : Piece
  ok1 : q1.Ok R₀
  ok2 : q2.Ok R₀
  ok3 : q3.Ok R₀
  h0 : q1.start = 0
  h12 : q1.stop = q2.start
  h23 : q2.stop = q3.start
  h3 : q3.stop = p

/-- Integral of `f` along the chain. -/
noncomputable def Chain3.int {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (f : ℂ → ℂ) : ℂ :=
  lineInt ch.q1.z0 ch.q1.d ch.q1.a ch.q1.b f + lineInt ch.q2.z0 ch.q2.d ch.q2.a ch.q2.b f +
    lineInt ch.q3.z0 ch.q3.d ch.q3.a ch.q3.b f

/-- Path independence of `s^{1/2} g(s)` along a chain: `∫ = Φ(p) - Φ(0)`. -/
theorem Chain3.int_csr {R₀ : ℝ} {p : ℂ} (hR : 0 < R₀) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 R₀))
    (ch : Chain3 R₀ p) :
    ∃ Φ : ℂ → ℂ, ch.int (fun z => csr z * g z) = Φ p - Φ 0 := by
  obtain ⟨Φ, hΦ⟩ := lineInt_csr hR hg
  refine ⟨Φ, ?_⟩
  have e1 := hΦ ch.q1.z0 ch.q1.d ch.q1.a ch.q1.b ch.ok1.1 ch.ok1.2.1 ch.ok1.2.2
  have e2 := hΦ ch.q2.z0 ch.q2.d ch.q2.a ch.q2.b ch.ok2.1 ch.ok2.2.1 ch.ok2.2.2
  have e3 := hΦ ch.q3.z0 ch.q3.d ch.q3.a ch.q3.b ch.ok3.1 ch.ok3.2.1 ch.ok3.2.2
  unfold Chain3.int
  rw [e1, e2, e3]
  have h0 : ch.q1.z0 + (ch.q1.a : ℂ) * ch.q1.d = 0 := ch.h0
  have h12 : ch.q1.z0 + (ch.q1.b : ℂ) * ch.q1.d = ch.q2.z0 + (ch.q2.a : ℂ) * ch.q2.d := ch.h12
  have h23 : ch.q2.z0 + (ch.q2.b : ℂ) * ch.q2.d = ch.q3.z0 + (ch.q3.a : ℂ) * ch.q3.d := ch.h23
  have h3 : ch.q3.z0 + (ch.q3.b : ℂ) * ch.q3.d = p := ch.h3
  rw [h0, h12, h23, h3]
  ring

/-- Fundamental theorem of calculus along a chain, for a function `Ψ` which is continuous on the chain and has derivative `Ψ'`
at the interior parameters, with `Ψ'` interval integrable on each piece. -/
theorem Chain3.int_ftc {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) {Ψ Ψ' : ℂ → ℂ}
    (hcont : ∀ q ∈ [ch.q1, ch.q2, ch.q3], ContinuousOn (fun t : ℝ => Ψ (q.z0 + (t : ℂ) * q.d)) (Icc q.a q.b))
    (hder : ∀ q ∈ [ch.q1, ch.q2, ch.q3], ∀ t ∈ Ioo q.a q.b,
      HasDerivAt Ψ (Ψ' (q.z0 + (t : ℂ) * q.d)) (q.z0 + (t : ℂ) * q.d))
    (hint : ∀ q ∈ [ch.q1, ch.q2, ch.q3],
      IntervalIntegrable (fun t : ℝ => Ψ' (q.z0 + (t : ℂ) * q.d) * q.d) volume q.a q.b) :
    ch.int Ψ' = Ψ p - Ψ 0 := by
  have piece : ∀ q ∈ [ch.q1, ch.q2, ch.q3], lineInt q.z0 q.d q.a q.b Ψ' = Ψ q.stop - Ψ q.start := by
    intro q hq
    have hab : q.a ≤ q.b := by
      rcases List.mem_cons.mp hq with h | h
      · rw [h]; exact ch.ok1.1
      · rcases List.mem_cons.mp h with h | h
        · rw [h]; exact ch.ok2.1
        · rw [List.mem_singleton.mp h]; exact ch.ok3.1
    unfold lineInt
    have hd : ∀ t ∈ Ioo q.a q.b, HasDerivAt (fun t : ℝ => Ψ (q.z0 + (t : ℂ) * q.d)) (Ψ' (q.z0 + (t : ℂ) * q.d) * q.d) t := by
      intro t ht
      have h := (hder q hq t ht).scomp t (hasDerivAt_line q.z0 q.d t)
      have e : Ψ' (q.z0 + (t : ℂ) * q.d) * q.d = q.d • Ψ' (q.z0 + (t : ℂ) * q.d) := by rw [smul_eq_mul]; ring
      rw [e]; exact h
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hcont q hq) hd (hint q hq)
  unfold Chain3.int
  rw [piece ch.q1 (by simp), piece ch.q2 (by simp), piece ch.q3 (by simp)]
  have h0 : ch.q1.start = 0 := ch.h0
  have h12 := ch.h12
  have h23 := ch.h23
  have h3 := ch.h3
  rw [h0, h12, h23, h3]
  ring

lemma re_line_d6 (t : ℝ) : (0 + (t : ℂ) * d6).re = t * (Real.sqrt 3 / 2) := by
  simp [Complex.mul_re, d6_re, d6_im]

lemma pieceA_ok {R R₀ : ℝ} (hR : 0 ≤ R) (hRR : R < R₀) : Piece.Ok R₀ ((0 : ℂ), d6, (0 : ℝ), R) := by
  refine ⟨hR, ?_, ?_⟩
  · intro t ht
    have ht' : (0 : ℝ) ≤ t ∧ t ≤ R := ht
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have := norm_ray ht'.1
      simp only [Piece.z0, Piece.d]
      rw [this]; linarith [ht'.2]
    · simp only [Piece.z0, Piece.d]
      rw [re_line_d6]; have := Real.sqrt_nonneg 3; nlinarith [ht'.1]
  · intro t ht
    have ht' : (0 : ℝ) < t ∧ t ≤ R := ht
    simp only [Piece.z0, Piece.d]
    intro h0
    have := norm_ray ht'.1.le
    rw [h0, norm_zero] at this
    linarith [ht'.1]

lemma pieceA_deg_ok {R R₀ : ℝ} (hR : 0 ≤ R) (hRR : R < R₀) : Piece.Ok R₀ ((0 : ℂ), d6, R, R) := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro t ht
    have htR : t = R := le_antisymm ht.2 ht.1
    subst htR
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      simp only [Piece.z0, Piece.d]
      rw [norm_ray hR]; exact hRR
    · simp only [Piece.z0, Piece.d]
      rw [re_line_d6]; have := Real.sqrt_nonneg 3; nlinarith
  · intro t ht
    exact absurd ht.1 (not_lt.mpr ht.2)

/-- The ray chain `0 → R e^{iπ/6}`. -/
noncomputable def chainA {R R₀ : ℝ} (hR : 0 ≤ R) (hRR : R < R₀) : Chain3 R₀ ((R : ℂ) * d6) where
  q1 := ((0 : ℂ), d6, (0 : ℝ), R)
  q2 := ((0 : ℂ), d6, R, R)
  q3 := ((0 : ℂ), d6, R, R)
  ok1 := pieceA_ok hR hRR
  ok2 := pieceA_deg_ok hR hRR
  ok3 := pieceA_deg_ok hR hRR
  h0 := by simp [Piece.start, Piece.z0, Piece.a, Piece.d]
  h12 := by simp [Piece.start, Piece.stop, Piece.z0, Piece.a, Piece.b, Piece.d]
  h23 := by simp [Piece.start, Piece.stop, Piece.z0, Piece.a, Piece.b, Piece.d]
  h3 := by simp [Piece.stop, Piece.z0, Piece.b, Piece.d]

/-- The junction parameter `u_J = (1+√3)/2`. -/
noncomputable def uJ : ℝ := (1 + Real.sqrt 3) / 2

lemma uJ_bounds : 0 ≤ uJ ∧ uJ ≤ 3 / 2 := by
  have h0 := Real.sqrt_nonneg 3
  have h1 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  unfold uJ; constructor <;> linarith

lemma pieceB1_ok {v R₀ : ℝ} (hv : 0 < v) (h3 : 3 * v < R₀) :
    Piece.Ok R₀ ((0 : ℂ), (v : ℂ) * (1 - Complex.I), (0 : ℝ), (1 / 2 : ℝ)) := by
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  refine ⟨by show (0 : ℝ) ≤ 1 / 2; norm_num, ?_, ?_⟩
  · intro t ht
    have ht' : (0 : ℝ) ≤ t ∧ t ≤ 1 / 2 := ht
    simp only [Piece.z0, Piece.d]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_seg1 hv.le ht'.1]
      have := Real.sqrt_nonneg 2
      nlinarith [mul_nonneg this hv.le, mul_nonneg (mul_nonneg this hv.le) ht'.1]
    · simp [Complex.mul_re, Complex.mul_im]
      nlinarith [ht'.1]
  · intro t ht
    have ht' : (0 : ℝ) < t ∧ t ≤ 1 / 2 := ht
    have ht0 : 0 < t := ht'.1
    simp only [Piece.z0, Piece.d]
    intro h0
    have h := norm_seg1 hv.le ht0.le
    rw [h0, norm_zero] at h
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have : 0 < Real.sqrt 2 * v * t := by positivity
    linarith

lemma pieceB2_ok {v R₀ : ℝ} (hv : 0 < v) (h3 : 3 * v < R₀) :
    Piece.Ok R₀ ((v : ℂ), (v : ℂ) * (1 + Complex.I), (-(1 / 2 : ℝ)), uJ) := by
  obtain ⟨hu0, hu1⟩ := uJ_bounds
  refine ⟨by show -(1 / 2 : ℝ) ≤ uJ; linarith, ?_, ?_⟩
  · intro t ht
    have ht' : -(1 / 2 : ℝ) ≤ t ∧ t ≤ uJ := ht
    simp only [Piece.z0, Piece.d]
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_seg2 hv.le]
      have hq : Real.sqrt ((1 + t) ^ 2 + t ^ 2) ≤ 3 := by
        rw [Real.sqrt_le_left (by norm_num)]
        nlinarith [ht'.1, ht'.2]
      nlinarith [mul_le_mul_of_nonneg_left hq hv.le]
    · simp [Complex.mul_re, Complex.mul_im]
      nlinarith [ht'.1]
  · intro t ht
    have ht' : -(1 / 2 : ℝ) < t ∧ t ≤ uJ := ht
    simp only [Piece.z0, Piece.d]
    intro h0
    have hre : 0 < (↑v + ↑t * (↑v * (1 + Complex.I)) : ℂ).re := by
      simp [Complex.mul_re, Complex.mul_im]
      nlinarith [ht'.1]
    rw [h0] at hre
    simp at hre

lemma pieceB3_ok {v R R₀ : ℝ} (hv : 0 < v) (hR : (1 + Real.sqrt 3) * v ≤ R) (hRR : R < R₀) :
    Piece.Ok R₀ ((0 : ℂ), d6, (1 + Real.sqrt 3) * v, R) := by
  have hs3 : 1 ≤ Real.sqrt 3 := by rw [Real.one_le_sqrt]; norm_num
  have hrJ : 0 < (1 + Real.sqrt 3) * v := by positivity
  refine ⟨hR, ?_, ?_⟩
  · intro t ht
    have ht' : (1 + Real.sqrt 3) * v ≤ t ∧ t ≤ R := ht
    have ht0 : 0 ≤ t := hrJ.le.trans ht'.1
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      simp only [Piece.z0, Piece.d]
      rw [norm_ray ht0]; linarith [ht'.2]
    · simp only [Piece.z0, Piece.d]
      rw [re_line_d6]; have := Real.sqrt_nonneg 3; nlinarith
  · intro t ht
    have ht' : (1 + Real.sqrt 3) * v < t ∧ t ≤ R := ht
    simp only [Piece.z0, Piece.d]
    intro h0
    have := norm_ray (hrJ.trans ht'.1).le
    rw [h0, norm_zero] at this
    linarith [hrJ.trans ht'.1]

/-- The polygonal chain `0 → v(1-i)/2 → (1+√3) v e^{iπ/6} → R e^{iπ/6}`. -/
noncomputable def chainB {v R R₀ : ℝ} (hv : 0 < v) (hR : (1 + Real.sqrt 3) * v ≤ R) (hRR : R < R₀)
    (h3 : 3 * v < R₀) : Chain3 R₀ ((R : ℂ) * d6) where
  q1 := ((0 : ℂ), (v : ℂ) * (1 - Complex.I), (0 : ℝ), (1 / 2 : ℝ))
  q2 := ((v : ℂ), (v : ℂ) * (1 + Complex.I), (-(1 / 2 : ℝ)), uJ)
  q3 := ((0 : ℂ), d6, (1 + Real.sqrt 3) * v, R)
  ok1 := pieceB1_ok hv h3
  ok2 := pieceB2_ok hv h3
  ok3 := pieceB3_ok hv hR hRR
  h0 := by simp [Piece.start, Piece.z0, Piece.a, Piece.d]
  h12 := by
    simp only [Piece.start, Piece.stop, Piece.z0, Piece.a, Piece.b, Piece.d]
    push_cast; ring
  h23 := by
    simp only [Piece.start, Piece.stop, Piece.z0, Piece.a, Piece.b, Piece.d, uJ]
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, d6_re, d6_im]
      nlinarith [sqrt3_sq]
    · simp [Complex.mul_re, Complex.mul_im, d6_re, d6_im]
      ring
  h3 := by simp [Piece.stop, Piece.z0, Piece.b, Piece.d]

/-- The `α`-moment of the phase modulus along a chain. -/
noncomputable def Chain3.mom {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U α : ℝ) : ℝ :=
  (∫ t in ch.q1.a..ch.q1.b, ‖ch.q1.z0 + (t : ℂ) * ch.q1.d‖ ^ α *
      Real.exp (-(PhU U (ch.q1.z0 + (t : ℂ) * ch.q1.d)).im) * ‖ch.q1.d‖) +
    (∫ t in ch.q2.a..ch.q2.b, ‖ch.q2.z0 + (t : ℂ) * ch.q2.d‖ ^ α *
      Real.exp (-(PhU U (ch.q2.z0 + (t : ℂ) * ch.q2.d)).im) * ‖ch.q2.d‖) +
    (∫ t in ch.q3.a..ch.q3.b, ‖ch.q3.z0 + (t : ℂ) * ch.q3.d‖ ^ α *
      Real.exp (-(PhU U (ch.q3.z0 + (t : ℂ) * ch.q3.d)).im) * ‖ch.q3.d‖)

lemma chainA_mom {R R₀ : ℝ} (hR : 0 ≤ R) (hRR : R < R₀) (U α : ℝ) :
    (chainA hR hRR).mom U α = ∫ t in (0 : ℝ)..R, t ^ α * Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
  unfold Chain3.mom
  simp only [chainA, Piece.z0, Piece.d, Piece.a, Piece.b, intervalIntegral.integral_same, add_zero]
  exact ray_moment_eq U R α hR

lemma chainB_mom {v R R₀ : ℝ} (hv : 0 < v) (hR : (1 + Real.sqrt 3) * v ≤ R) (hRR : R < R₀)
    (h3 : 3 * v < R₀) (α : ℝ) :
    (chainB hv hR hRR h3).mom (-(v ^ 2) / kap) α =
      (∫ t in (0 : ℝ)..(1 / 2), (Real.sqrt 2 * v * t) ^ α * Real.exp (-(v ^ 3 * (t - 2 / 3 * t ^ 3))) *
        (Real.sqrt 2 * v)) +
      (∫ t in (-(1 / 2 : ℝ))..uJ, (v * Real.sqrt ((1 + t) ^ 2 + t ^ 2)) ^ α *
        Real.exp (-(v ^ 3 * (t ^ 2 * (2 + 2 / 3 * t)))) * (Real.sqrt 2 * v)) +
      (∫ t in ((1 + Real.sqrt 3) * v)..R, t ^ α * Real.exp (-(t ^ 3 / 3 - v ^ 2 / 2 * t))) := by
  have hrJ : 0 ≤ (1 + Real.sqrt 3) * v := by positivity
  unfold Chain3.mom
  simp only [chainB, Piece.z0, Piece.d, Piece.a, Piece.b]
  rw [seg1_moment_eq hv.le α, seg2_moment_eq hv.le α uJ, seg3_moment_eq hrJ hR α]

/-- The three moment bounds `ct:sd-moments` for a chain at parameter `U`. -/
def MomOK {R₀ : ℝ} {p : ℂ} (C U : ℝ) (ch : Chain3 R₀ p) : Prop :=
  ch.mom U (-(1 / 2 : ℝ)) ≤ C * (1 + |U|) ^ (-(1 / 2 : ℝ)) ∧ ch.mom U (1 / 2 : ℝ) ≤ C ∧
    ch.mom U (3 / 2 : ℝ) ≤ C * (1 + |U|) ^ (1 / 2 : ℝ)

lemma one_le_rpow_half (U : ℝ) : 1 ≤ (1 + |U|) ^ (1 / 2 : ℝ) :=
  Real.one_le_rpow (by linarith [abs_nonneg U]) (by norm_num)

theorem chainA_momOK : ∃ C : ℝ, 0 ≤ C ∧ ∀ (U R R₀ : ℝ) (hU : -1 ≤ U) (hR : 0 ≤ R) (hRR : R < R₀),
    MomOK C U (chainA hR hRR) := by
  obtain ⟨C1, hC1, h1⟩ := momA_const (α := 1 / 2) (by norm_num)
  obtain ⟨C2, hC2, h2⟩ := momA_const (α := 3 / 2) (by norm_num)
  obtain ⟨C3, hC3, h3⟩ := momA_inv
  refine ⟨C1 + C2 + C3, by positivity, fun U R R₀ hU hR hRR => ⟨?_, ?_, ?_⟩⟩
  · rw [chainA_mom]
    have e : -(1 / 2 : ℝ) = -(1 : ℝ) / 2 := by norm_num
    rw [e]
    refine (h3 U R hU hR).trans ?_
    have : 0 ≤ (1 + |U|) ^ (-(1 : ℝ) / 2) := by positivity
    nlinarith [mul_nonneg hC1 this, mul_nonneg hC2 this]
  · rw [chainA_mom]
    exact (h1 U R hU hR).trans (by linarith)
  · rw [chainA_mom]
    refine (h2 U R hU hR).trans ?_
    have := one_le_rpow_half U
    nlinarith [mul_nonneg hC1 (by linarith : (0 : ℝ) ≤ (1 + |U|) ^ (1 / 2 : ℝ) - 1),
      mul_nonneg hC3 (by linarith : (0 : ℝ) ≤ (1 + |U|) ^ (1 / 2 : ℝ) - 1),
      mul_nonneg hC2 (by linarith : (0 : ℝ) ≤ (1 + |U|) ^ (1 / 2 : ℝ) - 1)]

lemma kap_ge_one : 1 ≤ kap := by
  unfold kap CtAiry.kap
  exact Real.one_le_rpow (by norm_num) (by norm_num)

lemma abs_U_B {v : ℝ} (hv : 0 ≤ v) : |-(v ^ 2) / kap| = v ^ 2 / kap := by
  rw [neg_div, abs_neg, abs_of_nonneg (by have := kap_pos; positivity)]

lemma inv_v_le {v : ℝ} (hv : 0 < v) (hvk : kap ≤ v ^ 2) :
    v ^ (-(1 : ℝ)) ≤ Real.sqrt (2 / kap) * (1 + |-(v ^ 2) / kap|) ^ (-(1 / 2 : ℝ)) := by
  have hk := kap_pos
  rw [abs_U_B hv.le, Real.rpow_neg_one, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt (1 + v ^ 2 / kap) ≤ Real.sqrt (2 / kap) * v := by
    have e : Real.sqrt (2 / kap) * v = Real.sqrt (2 / kap * v ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv.le]
    rw [e]
    apply Real.sqrt_le_sqrt
    have h1' : 1 ≤ v ^ 2 / kap := (one_le_div hk).mpr hvk
    have e2 : 2 / kap * v ^ 2 = v ^ 2 / kap + v ^ 2 / kap := by ring
    linarith
  have hs : 0 < Real.sqrt (1 + v ^ 2 / kap) := Real.sqrt_pos.mpr (by positivity)
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hv hs]
  linarith

lemma v_le_sqrt {v : ℝ} (hv : 0 < v) :
    v ≤ Real.sqrt kap * (1 + |-(v ^ 2) / kap|) ^ (1 / 2 : ℝ) := by
  have hk := kap_pos
  rw [abs_U_B hv.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hk.le]
  apply Real.le_sqrt_of_sq_le
  have : kap * (1 + v ^ 2 / kap) = kap + v ^ 2 := by field_simp
  rw [this]; nlinarith

theorem chainB_momOK : ∃ C : ℝ, 0 ≤ C ∧ ∀ (v R R₀ : ℝ) (hv : 0 < v) (hvk : kap ≤ v ^ 2)
    (hR : (1 + Real.sqrt 3) * v ≤ R) (hRR : R < R₀) (h3 : 3 * v < R₀),
    MomOK C (-(v ^ 2) / kap) (chainB hv hR hRR h3) := by
  obtain ⟨A1, hA1, a1⟩ := momB1 (α := -(1 / 2 : ℝ)) (by norm_num)
  obtain ⟨A2, hA2, a2⟩ := momB1 (α := 1 / 2) (by norm_num)
  obtain ⟨A3, hA3, a3⟩ := momB1 (α := 3 / 2) (by norm_num)
  obtain ⟨B1, hB1, b1⟩ := momB2 (α := -(1 / 2 : ℝ)) le_rfl (by norm_num)
  obtain ⟨B2, hB2, b2⟩ := momB2 (α := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨B3, hB3, b3⟩ := momB2 (α := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨D1, hD1, d1⟩ := momB3 (α := -(1 / 2 : ℝ)) le_rfl (by norm_num)
  obtain ⟨D2, hD2, d2⟩ := momB3 (α := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨D3, hD3, d3⟩ := momB3 (α := 3 / 2) (by norm_num) (by norm_num)
  set S : ℝ := A1 + A2 + A3 + B1 + B2 + B3 + D1 + D2 + D3 with hS
  have hS0 : 0 ≤ S := by positivity
  have hsk := Real.sqrt_nonneg kap
  have hs2k := Real.sqrt_nonneg (2 / kap)
  refine ⟨S * (1 + Real.sqrt (2 / kap) + Real.sqrt kap), by positivity, ?_⟩
  intro v R R₀ hv hvk hR hRR h3
  have hv1 : 1 ≤ v := by nlinarith [kap_ge_one]
  have hinv := inv_v_le hv hvk
  have hvl := v_le_sqrt hv
  set X : ℝ := 1 + |-(v ^ 2) / kap| with hX
  have hX1 : 1 ≤ X := by rw [hX]; linarith [abs_nonneg (-(v ^ 2) / kap)]
  have hXp : 1 ≤ X ^ (1 / 2 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hXm : 0 ≤ X ^ (-(1 / 2 : ℝ)) := by positivity
  have pw1 : v ^ (-2 * (-(1 / 2 : ℝ) + 1)) = v ^ (-(1 : ℝ)) := by congr 1; norm_num
  have pw2 : v ^ (-2 * (1 / 2 + 1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by norm_num)
  have pw3 : v ^ (-2 * (3 / 2 + 1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by norm_num)
  have pb1 : v ^ (-(1 / 2 : ℝ) - 1 / 2) = v ^ (-(1 : ℝ)) := by congr 1; norm_num
  have pb2 : v ^ ((1 / 2 : ℝ) - 1 / 2) = 1 := by norm_num
  have pb3 : v ^ ((3 / 2 : ℝ) - 1 / 2) = v := by
    rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num, Real.rpow_one]
  have pvm : v ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv1 (by norm_num)
  have pvm0 : 0 ≤ v ^ (-(1 : ℝ)) := by positivity
  have hu0 : -(1 / 2 : ℝ) ≤ uJ := by linarith [uJ_bounds.1]
  have x1 := a1 v hv1
  have x2 := a2 v hv1
  have x3 := a3 v hv1
  have y1 := b1 v uJ hv1 hu0
  have y2 := b2 v uJ hv1 hu0
  have y3 := b3 v uJ hv1 hu0
  have z1 := d1 v R hv1 hR
  have z2 := d2 v R hv1 hR
  have z3 := d3 v R hv1 hR
  rw [pw1] at x1
  rw [pb1] at y1
  rw [pb2] at y2
  rw [pb3] at y3
  have w2 : A2 * v ^ (-2 * (1 / 2 + 1 : ℝ)) ≤ A2 := by
    linarith only [mul_le_mul_of_nonneg_left pw2 hA2]
  have w3 : A3 * v ^ (-2 * (3 / 2 + 1 : ℝ)) ≤ A3 := by
    linarith only [mul_le_mul_of_nonneg_left pw3 hA3]
  have hsum : A1 + A2 + A3 + B1 + B2 + B3 + D1 + D2 + D3 = S := hS.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [chainB_mom hv hR hRR h3]
    have hq : A1 + B1 + D1 ≤ S := by linarith only [hsum, hA2, hA3, hB2, hB3, hD2, hD3]
    have h1 : (A1 + B1 + D1) * v ^ (-(1 : ℝ)) ≤
        (A1 + B1 + D1) * (Real.sqrt (2 / kap) * X ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have h2 := mul_le_mul_of_nonneg_right hq (mul_nonneg hs2k hXm)
    have h3' := mul_nonneg (mul_nonneg hS0 (by linarith only [hsk] : (0 : ℝ) ≤ 1 + Real.sqrt kap)) hXm
    linarith only [x1, y1, z1, h1, h2, h3']
  · rw [chainB_mom hv hR hRR h3]
    have h1 := mul_le_mul_of_nonneg_left pvm hD2
    have h2 := mul_nonneg hS0 (add_nonneg hs2k hsk)
    have hq : A2 + B2 + D2 ≤ S := by linarith only [hsum, hA1, hA3, hB1, hB3, hD1, hD3]
    linarith only [x2, y2, z2, w2, h1, h2, hq]
  · rw [chainB_mom hv hR hRR h3]
    have h1 := mul_le_mul_of_nonneg_left pvm hD3
    have h2 := mul_nonneg hA3 (sub_nonneg.2 hv1)
    have h3' := mul_nonneg hD3 (sub_nonneg.2 hv1)
    have hq : A3 + B3 + D3 ≤ S := by linarith only [hsum, hA1, hA2, hB1, hB2, hD1, hD2]
    have h4 : (A3 + B3 + D3) * v ≤ (A3 + B3 + D3) * (Real.sqrt kap * X ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hvl (by positivity)
    have h5 := mul_le_mul_of_nonneg_right hq (mul_nonneg hsk (zero_le_one.trans hXp))
    have h6 := mul_nonneg (mul_nonneg hS0 (by linarith only [hs2k] : (0 : ℝ) ≤ 1 + Real.sqrt (2 / kap)))
      (zero_le_one.trans hXp)
    linarith only [x3, y3, z3, w3, h1, h2, h3', h4, h5, h6]

end FormalResearch.SignUncertainty.CtSd
