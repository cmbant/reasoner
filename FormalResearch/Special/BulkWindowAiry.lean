module

public import FormalResearch.Special.AiryPositive
public import FormalResearch.Special.AiryGammaBounds
public import FormalResearch.Special.AiryEnvelopeNeg
public import FormalResearch.Special.AiryRecessiveSums
public import FormalResearch.Special.DiscreteAiryOscBi

/-!
# Bulk window, part 1: local facts on `Ai` used to count the nodes of the Airy window

Self-contained facts about the Airy function `Ai` (`y'' = x y`), used to read the sign changes of a lattice sampling
`Y_k = κ g_k Ai(X_k) + (small)` of `Ai` (the Airy window of the `3j` chain) off the zeros of `Ai`:

* `bwn_taylor`: second-order Taylor bound `|f(t) - f(x) - f'(x)(t-x)| ≤ K (t-x)²/2` on `[x-w, x+w]` when `|f''| ≤ K` there.
* `bwn_E_anti`, `bwn_c0`, `bwn_E_ge`: the energy `E(t) = Ai'(t)² - t Ai(t)²` has `E' = -Ai² ≤ 0`, hence `Ai'(x)² + |x| Ai(x)² ≥ c₀²`
  for `x ≤ 0`, `c₀ = |Ai'(0)| > 0`.
* **`bwn_nz`** (a near-zero lattice point is isolated and its neighbours have opposite signs): if `x ≤ -1`, `|Ai x| ≤ ε` and
  `(-x) ε² ≤ c₀²/2`, then for steps `d, d' > 0` with `d √(-x) ≤ 1/4`, `d' √(-x) ≤ 1/4`, `8 ε ≤ c₀ d`, `8 ε ≤ c₀ d'` there is a sign
  `s = ±1` with `ε < s Ai(x + d)` and `ε < -s Ai(x - d')`.
* `bwn_pos_const`: `Ai ≥ c_pos > 0` on `[-1, 1/4]`; `bwn_wt_le`: `airyWt ≤ 1`, `airyBiWt ≤ 3`, `|Bi| ≤ 1350` on `X ≤ 1/4`.

**Claim class: proved.**  **Not formalised:** sharp constants (all constants are far from optimal); nothing about the lattice or the
`3j` chain (that is `BulkWindowCount`, `BulkWindowChart`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special


lemma bwn_taylor_right {f f1 f2 : ℝ → ℝ} {x w K : ℝ}
    (h1 : ∀ t, HasDerivAt f (f1 t) t) (h2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hb : ∀ t ∈ Icc x (x + w), |f2 t| ≤ K) :
    ∀ t ∈ Icc x (x + w), |f t - f x - f1 x * (t - x)| ≤ K * (t - x) ^ 2 / 2 := by
  have hconv : Convex ℝ (Icc x (x + w)) := convex_Icc _ _
  have hlip : ∀ t ∈ Icc x (x + w), |f1 t - f1 x| ≤ K * (t - x) := by
    intro t ht
    have hx : x ∈ Icc x (x + w) := ⟨le_rfl, by linarith [ht.1, ht.2]⟩
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f1) (f' := f2) (C := K)
      (fun s _ => (h2 s).hasDerivWithinAt) (fun s hs => by simpa using hb s hs) hx ht
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.1)] using this
  have hd1 : ∀ t, HasDerivAt (fun t => f t - f x - f1 x * (t - x) + K * (t - x) ^ 2 / 2)
      (f1 t - f1 x + K * (t - x)) t := by
    intro t
    have a := (h1 t).sub_const (f x)
    have b := ((hasDerivAt_id t).sub_const x).const_mul (f1 x)
    have c := (((hasDerivAt_id t).sub_const x).pow 2).const_mul K |>.div_const 2
    have := (a.sub b).add c
    convert this using 1
    · funext s; simp
    · simp; ring
  have hd2 : ∀ t, HasDerivAt (fun t => f t - f x - f1 x * (t - x) - K * (t - x) ^ 2 / 2)
      (f1 t - f1 x - K * (t - x)) t := by
    intro t
    have a := (h1 t).sub_const (f x)
    have b := ((hasDerivAt_id t).sub_const x).const_mul (f1 x)
    have c := (((hasDerivAt_id t).sub_const x).pow 2).const_mul K |>.div_const 2
    have := (a.sub b).sub c
    convert this using 1
    · funext s; simp
    · simp; ring
  have m1 : MonotoneOn (fun t => f t - f x - f1 x * (t - x) + K * (t - x) ^ 2 / 2) (Icc x (x + w)) := by
    refine monotoneOn_of_deriv_nonneg hconv (fun t _ => (hd1 t).continuousAt.continuousWithinAt)
      (fun t _ => (hd1 t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hd1 t).deriv]
    have := hlip t (interior_subset ht)
    have := (abs_le.1 this).1
    linarith
  have m2 : AntitoneOn (fun t => f t - f x - f1 x * (t - x) - K * (t - x) ^ 2 / 2) (Icc x (x + w)) := by
    refine antitoneOn_of_deriv_nonpos hconv (fun t _ => (hd2 t).continuousAt.continuousWithinAt)
      (fun t _ => (hd2 t).differentiableAt.differentiableWithinAt) (fun t ht => ?_)
    rw [(hd2 t).deriv]
    have := hlip t (interior_subset ht)
    have := (abs_le.1 this).2
    linarith
  intro t ht
  have hx : x ∈ Icc x (x + w) := ⟨le_rfl, by linarith [ht.1, ht.2]⟩
  have a1 := m1 hx ht ht.1
  have a2 := m2 hx ht ht.1
  simp at a1 a2
  rw [abs_le]; constructor <;> linarith


/-- Two-sided version (reflect `t ↦ 2x - t`). -/
lemma bwn_taylor {f f1 f2 : ℝ → ℝ} {x w K : ℝ}
    (h1 : ∀ t, HasDerivAt f (f1 t) t) (h2 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hb : ∀ t ∈ Icc (x - w) (x + w), |f2 t| ≤ K) :
    ∀ t ∈ Icc (x - w) (x + w), |f t - f x - f1 x * (t - x)| ≤ K * (t - x) ^ 2 / 2 := by
  intro t ht
  rcases le_total x t with hxt | hxt
  · exact bwn_taylor_right h1 h2 (fun s hs => hb s ⟨by linarith [hs.1, ht.1, ht.2, hs.2], hs.2⟩) t ⟨hxt, ht.2⟩
  · -- reflect
    have g1 : ∀ s, HasDerivAt (fun s => f (2 * x - s)) (-f1 (2 * x - s)) s := by
      intro s
      have := (h1 (2 * x - s)).comp s ((hasDerivAt_id s).const_sub (2 * x))
      simpa [Function.comp_def] using this
    have g2 : ∀ s, HasDerivAt (fun s => -f1 (2 * x - s)) (f2 (2 * x - s)) s := by
      intro s
      have := (h2 (2 * x - s)).comp s ((hasDerivAt_id s).const_sub (2 * x))
      have h3 := this.neg
      convert h3 using 1
      · funext s; simp [Function.comp_def]
      · simp
    have := bwn_taylor_right g1 g2 (x := x) (w := w) (K := K)
      (fun s hs => hb _ ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩) (2 * x - t)
      ⟨by linarith, by linarith [ht.1]⟩
    have e : 2 * x - (2 * x - t) = t := by ring
    simp only [e] at this
    have e2 : 2 * x - x = x := by ring
    simp only [e2] at this
    have e3 : (2 * x - t - x) = x - t := by ring
    rw [e3] at this
    convert this using 2
    · ring_nf
    · ring


noncomputable def bwn_E (t : ℝ) : ℝ := airyAi' t ^ 2 - t * airyAi t ^ 2

lemma bwn_hasDerivAt_E (t : ℝ) : HasDerivAt bwn_E (-(airyAi t) ^ 2) t := by
  have a := (hasDerivAt_airyAi' t).pow 2
  have b := (hasDerivAt_id t).mul ((hasDerivAt_airyAi t).pow 2)
  have := a.sub b
  convert this using 1
  · funext s; simp [bwn_E]
  · simp; ring

lemma bwn_E_anti : Antitone bwn_E :=
  antitone_of_deriv_nonpos (fun t => (bwn_hasDerivAt_E t).differentiableAt)
    (fun t => by rw [(bwn_hasDerivAt_E t).deriv]; nlinarith [sq_nonneg (airyAi t)])

noncomputable def bwn_c0 : ℝ := |airyAi' 0|

lemma bwn_c0_pos : 0 < bwn_c0 := by
  have := airyAi'_neg (le_refl (0 : ℝ))
  unfold bwn_c0; exact abs_pos.2 this.ne

lemma bwn_E_ge {x : ℝ} (hx : x ≤ 0) : bwn_c0 ^ 2 ≤ airyAi' x ^ 2 - x * airyAi x ^ 2 := by
  have := bwn_E_anti hx
  unfold bwn_E at this
  unfold bwn_c0; rw [sq_abs]; simpa using this


/-- Linearisation of `Ai` near a point `x ≤ -1` where `|Ai x| ≤ ε`: with `a = √(-x)`, for `0 < d ≤ 1/(4a)`,
`|Ai(x ± d) - Ai x ∓ Ai'(x) d| ≤ (5/64)(ε + d |Ai'(x)|)`. -/
lemma bwn_lin {x ε : ℝ} (hx : x ≤ -1) (hu : |airyAi x| ≤ ε) (hε : 0 ≤ ε) {d : ℝ} (hd : 0 ≤ d) (hdw : d * √(-x) ≤ 1 / 4) :
    |airyAi (x + d) - airyAi x - airyAi' x * d| ≤ 5 / 64 * (ε + d * |airyAi' x|) ∧
    |airyAi (x - d) - airyAi x + airyAi' x * d| ≤ 5 / 64 * (ε + d * |airyAi' x|) := by
  set a : ℝ := √(-x) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact Real.one_le_sqrt.2 (by linarith)
  have ha2 : a ^ 2 = -x := Real.sq_sqrt (by linarith)
  set w : ℝ := 1 / (4 * a) with hw
  have hw0 : 0 < w := by positivity
  have hdw' : d ≤ w := by rw [hw, le_div_iff₀ (by positivity)]; linarith
  have hw1 : w ≤ 1 / 4 := by rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set p := airyAi' x with hp
  set u := airyAi x with hu0
  set I := Icc (x - w) (x + w) with hI
  have hcont : Continuous airyAi := continuous_iff_continuousAt.2 fun t => (hasDerivAt_airyAi t).continuousAt
  obtain ⟨s, hsI, hsmax⟩ := (isCompact_Icc : IsCompact I).exists_isMaxOn (⟨x, ⟨by linarith, by linarith⟩⟩ : I.Nonempty)
    (hcont.abs.continuousOn)
  set S := |airyAi s| with hS
  have hS0 : 0 ≤ S := abs_nonneg _
  have hbS : ∀ t ∈ I, |airyAi t| ≤ S := fun t ht => hsmax ht
  have hb : ∀ t ∈ I, |t * airyAi t| ≤ 5 / 4 * (-x) * S := by
    intro t ht
    rw [abs_mul]
    have : |t| ≤ 5 / 4 * (-x) := by
      rw [abs_le]; constructor <;> nlinarith [ht.1, ht.2]
    exact mul_le_mul this (hbS t ht) (abs_nonneg _) (by nlinarith)
  have T := bwn_taylor (f := airyAi) (f1 := airyAi') (f2 := fun t => t * airyAi t) (x := x) (w := w)
    (K := 5 / 4 * (-x) * S) hasDerivAt_airyAi hasDerivAt_airyAi' hb
  -- bound on S
  have hws : (-x) * w ^ 2 = 1 / 16 := by rw [hw, ← ha2]; field_simp; ring
  have hSb : S ≤ 2 * (ε + |p| * w) := by
    have h1 := T s hsI
    have hsx : |s - x| ≤ w := by rw [abs_le]; constructor <;> linarith [hsI.1, hsI.2]
    have h2 : |airyAi s| ≤ |u| + |p| * |s - x| + 5 / 4 * (-x) * S * (s - x) ^ 2 / 2 := by
      have := abs_sub_abs_le_abs_sub (airyAi s) (u + p * (s - x))
      have h3 := abs_add_le u (p * (s - x))
      rw [abs_mul] at h3
      have h4 : |airyAi s - (u + p * (s - x))| ≤ 5 / 4 * (-x) * S * (s - x) ^ 2 / 2 := by
        simpa [sub_sub] using h1
      linarith
    have h5 : (s - x) ^ 2 ≤ w ^ 2 := by nlinarith [abs_nonneg (s - x), sq_abs (s - x)]
    have h6 : |p| * |s - x| ≤ |p| * w := mul_le_mul_of_nonneg_left hsx (abs_nonneg _)
    have h7 : 5 / 4 * (-x) * S * (s - x) ^ 2 / 2 ≤ 5 / 8 * S * (1 / 16) := by
      have : 5 / 4 * (-x) * S * (s - x) ^ 2 / 2 ≤ 5 / 8 * S * ((-x) * w ^ 2) := by
        have : (-x) * (s - x) ^ 2 ≤ (-x) * w ^ 2 := mul_le_mul_of_nonneg_left h5 (by linarith)
        nlinarith
      rw [hws] at this; exact this
    linarith
  -- the two sides
  have side : ∀ e : ℝ, |e| ≤ d → |airyAi (x + e) - u - p * e| ≤ 5 / 64 * (ε + d * |p|) := by
    intro e he
    have heI : x + e ∈ I := by
      rw [abs_le] at he; constructor <;> linarith [he.1, he.2]
    have h1 := T (x + e) heI
    simp only [add_sub_cancel_left] at h1
    refine h1.trans ?_
    have hae : (a * d) ^ 2 ≤ 1 / 16 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a) hd]
    have he2 : e ^ 2 ≤ d ^ 2 := by nlinarith [sq_abs e, abs_nonneg e]
    have hx2 : (-x) * d ^ 2 = (a * d) ^ 2 := by rw [mul_pow, ha2]
    have : 5 / 4 * (-x) * S * e ^ 2 / 2 ≤ 5 / 8 * S * ((a * d) ^ 2) := by
      rw [← hx2]
      have : (-x) * e ^ 2 ≤ (-x) * d ^ 2 := mul_le_mul_of_nonneg_left he2 (by linarith)
      nlinarith
    refine this.trans ?_
    have hSb' := hSb
    have hpw : (a * d) ^ 2 * (|p| * w) ≤ d * |p| / 16 := by
      have : (a * d) ^ 2 * w = (a * d) * d / 4 := by rw [hw]; field_simp
      calc (a * d) ^ 2 * (|p| * w) = |p| * ((a * d) ^ 2 * w) := by ring
        _ = |p| * ((a * d) * d / 4) := by rw [this]
        _ ≤ |p| * ((1 / 4) * d / 4) := by
          have : a * d ≤ 1 / 4 := by linarith [mul_comm d a]
          gcongr
        _ = d * |p| / 16 := by ring
    have hSq : S * (a * d) ^ 2 ≤ 2 * (ε + |p| * w) * (a * d) ^ 2 := mul_le_mul_of_nonneg_right hSb (sq_nonneg _)
    nlinarith [mul_nonneg hε (sub_nonneg.2 hae), sq_nonneg (a * d)]
  refine ⟨?_, ?_⟩
  · simpa using side d (by simp [abs_of_nonneg hd])
  · have := side (-d) (by simp [abs_of_nonneg hd])
    simpa [sub_eq_add_neg, mul_neg, neg_mul, add_assoc] using this


/-- **Sign change of `Ai` across a near-zero lattice point.**  If `x ≤ -1`, `|Ai x| ≤ ε` with `(-x) ε² ≤ c₀²/2` (`c₀ = |Ai'(0)|`)
then for steps `d, d' > 0` with `d √(-x) ≤ 1/4`, `d' √(-x) ≤ 1/4`, `8 ε ≤ c₀ d`, `8 ε ≤ c₀ d'` there is a sign `s = ±1`
with `ε < s Ai(x + d)` and `ε < -s Ai(x - d')`: both neighbours are beyond the tolerance and of opposite signs. -/
theorem bwn_nz {x ε d d' : ℝ} (hx : x ≤ -1) (hu : |airyAi x| ≤ ε) (hεc : -x * ε ^ 2 ≤ bwn_c0 ^ 2 / 2)
    (hd : 0 < d) (hd' : 0 < d') (hdw : d * √(-x) ≤ 1 / 4) (hdw' : d' * √(-x) ≤ 1 / 4)
    (hdε : 8 * ε ≤ bwn_c0 * d) (hdε' : 8 * ε ≤ bwn_c0 * d') :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ε < s * airyAi (x + d) ∧ ε < -s * airyAi (x - d') := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hu
  have hc := bwn_c0_pos
  have hE := bwn_E_ge (x := x) (by linarith)
  have hu2 : airyAi x ^ 2 ≤ ε ^ 2 := by
    have := sq_le_sq' (by linarith [abs_le.1 hu]) (abs_le.1 hu).2
    exact this
  have hp2 : bwn_c0 ^ 2 / 2 ≤ airyAi' x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hu2 (by linarith : (0 : ℝ) ≤ -x)]
  have hp : 7 / 10 * bwn_c0 ≤ |airyAi' x| := by
    by_contra hlt
    push Not at hlt
    nlinarith [sq_abs (airyAi' x), abs_nonneg (airyAi' x)]
  obtain ⟨l1, l2⟩ := bwn_lin hx hu hε hd.le hdw
  obtain ⟨m1, m2⟩ := bwn_lin hx hu hε hd'.le hdw'
  have k1 : 56 / 10 * ε ≤ |airyAi' x| * d := by nlinarith
  have k2 : 56 / 10 * ε ≤ |airyAi' x| * d' := by nlinarith
  have hpp : 0 < |airyAi' x| := by nlinarith
  have hu' := abs_le.1 hu
  have a1 := abs_le.1 l1
  have a2 := abs_le.1 l2
  have b1 := abs_le.1 m1
  have b2 := abs_le.1 m2
  rcases lt_or_gt_of_ne (abs_pos.1 hpp) with hneg | hpos
  · rw [abs_of_neg hneg] at k1 k2 a1 a2 b1 b2
    have q1 : 0 < -airyAi' x * d := mul_pos (neg_pos.2 hneg) hd
    have q2 : 0 < -airyAi' x * d' := mul_pos (neg_pos.2 hneg) hd'
    refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · linarith [a1.1, a1.2, hu'.1, hu'.2]
    · linarith [b2.1, b2.2, hu'.1, hu'.2]
  · rw [abs_of_pos hpos] at k1 k2 a1 a2 b1 b2
    have q1 : 0 < airyAi' x * d := mul_pos hpos hd
    have q2 : 0 < airyAi' x * d' := mul_pos hpos hd'
    refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · linarith [a1.1, a1.2, hu'.1, hu'.2]
    · linarith [b2.1, b2.2, hu'.1, hu'.2]


/-- `Ai ≥ c_pos > 0` on `[-1, 1/4]`. -/
lemma bwn_pos_const : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc (-1 : ℝ) (1 / 4), c ≤ airyAi x := by
  have hcont : Continuous airyAi := continuous_iff_continuousAt.2 fun t => (hasDerivAt_airyAi t).continuousAt
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) (1 / 4))).exists_isMinOn
    (⟨0, by norm_num, by norm_num⟩ : (Icc (-1 : ℝ) (1 / 4)).Nonempty) hcont.continuousOn
  exact ⟨airyAi x0, airyAi_pos_of_neg_one_le hx0.1, fun x hx => hmin hx⟩

/-- On `X ≤ 1/4`: `airyWt ≤ 1`, `airyBiWt ≤ 3` and `|Bi| ≤ 1350`. -/
lemma bwn_wt_le {X : ℝ} (hX : X ≤ 1 / 4) : airyWt X ≤ 1 ∧ airyBiWt X ≤ 3 ∧ |airyBi X| ≤ 1350 := by
  have h2 : (1 : ℝ) ≤ 2 + |X| := by linarith [abs_nonneg X]
  have hq : (2 + |X|) ^ (-(1 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2 (by norm_num)
  have hW : airyWt X ≤ 1 := (airyWt_le_rpow X).trans hq
  have hxi : airyXi X ≤ 1 / 12 := by
    have h1 := airyXi_mono hX
    have h3 : airyXi (1 / 4 : ℝ) = 1 / 12 := by
      rw [airyXi_eq_sqrt_pow]
      have : √(max (1 / 4 : ℝ) 0) = 1 / 2 := by
        rw [max_eq_left (by norm_num), show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]; norm_num
    linarith
  have he : Real.exp (airyXi X) ≤ 3 := by
    have h4 : Real.exp (airyXi X) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    have := Real.exp_one_lt_d9
    linarith
  have hB : airyBiWt X ≤ 3 := by
    unfold airyBiWt
    have := Real.exp_pos (airyXi X)
    have hq0 : 0 < (2 + |X|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  refine ⟨hW, hB, ?_⟩
  have := (apx_airyBi_global X).1
  linarith

/-- info: 'FormalResearch.Special.bwn_nz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.bwn_nz

end FormalResearch.Special
