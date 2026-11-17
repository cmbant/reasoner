module

public import FormalResearch.Special.AiryThm47Aux
public import FormalResearch.Special.AiryThm47Div
public import FormalResearch.Special.AiryThm47Band
public import FormalResearch.Special.AiryThm47Liouville

/-!
# Theorem 4.7, uniqueness half (`SOFT_EDGE_THEOREMS.md`, Theorem 4.7, proof of `≤` and uniqueness)

`at47_uniqueness`: for `N = P Ai + Q Ai'` with `(P, Q)` Hermite-Biehler, `Q ≠ 0`, and `S` the set of the `m = at47_m P Q` largest
zeros: an entire `f` of the class with `∫ f ≤ 0`, `f ≥ 0` on `S` and on `(-∞, um]`, `um ≥ tm = min S`, satisfies
`f ∏_{t∈S}(z - t) = c (-1)^m N²` with a constant `c ≥ 0` (`c = 0` if `um > tm`).  Proof: positivity step
(`airyPQ_nonneg_zeros_vanish`), local minima give double zeros, `entire_exists_div_sq`, polynomial bound on good circles
(`at47_G_circle_bound`), Liouville (`at47_entire_polynomial_of_circle_bound`), non-integrability (`at47_not_integrable_poly_mul`),
sign from `f ≥ 0` below `tm`, second derivative at `tm` when `um > tm`.  All proved.  The set `S` of the `m` largest zeros is a hypothesis
(it exists by `at47_top_zeros_min`); no ordered enumeration or one-zero-per-gap statement (Prüfer monotonicity) is formalised or needed.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter Topology

namespace FormalResearch.Special

/-- Arbitrarily negative real points where `N ≠ 0`. -/
lemma at47_exists_real_ne_zero {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (a : ℝ) :
    ∃ x : ℝ, x < a ∧ airyPQN P Q (x : ℂ) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set R : ℝ := |a| + 2 with hR
  have hfin := airyPQ_zeros_finite hHB R
  have hsub : (fun x : ℝ => (x : ℂ)) '' Set.Ioo (-R) a ⊆ {z : ℂ | airyPQN P Q z = 0 ∧ ‖z‖ ≤ R} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hcon x hx.2, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hx.1, hx.2, neg_abs_le a, le_abs_self a]
  have hlt : -R < a := by linarith [neg_abs_le a, le_abs_self a, abs_nonneg a]
  have hinf : (Set.Ioo (-R) a).Infinite := Set.Ioo_infinite hlt
  exact (hinf.image (Complex.ofReal_injective.injOn)).mono hsub |>.not_finite hfin |> fun h => h

/-- Polynomial growth of the quotient `G = f ∏(z-t) / N²` on the good circles. -/
lemma at47_G_circle_bound {P Q : ℝ[X]} (hQ : Q ≠ 0) (S : Finset ℝ) {f G : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hG : ∀ z, f z * at47_pr S z = G z * airyPQN P Q z ^ 2) :
    ∃ (n : ℕ) (C' : ℝ), 0 ≤ C' ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ z : ℂ, ‖z‖ = r → ‖G z‖ ≤ C' * (1 + r) ^ n := by
  obtain ⟨c, hc, k₀, hk₀⟩ := airyPQ_good_circle_SE5 P Q (Or.inr hQ)
  set T : ℝ := ∑ t ∈ S, |t| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set m := S.card
  refine ⟨⌈ν + m + 1 / 2⌉₊, C * (1 + T) ^ m / c, by positivity, fun R => ?_⟩
  obtain ⟨r, hr1, hr2, hr⟩ := hk₀ (max k₀ ⌈R⌉₊) (le_max_left _ _)
  refine ⟨r, (Nat.le_ceil R).trans ((by exact_mod_cast le_max_right k₀ ⌈R⌉₊ : (⌈R⌉₊ : ℝ) ≤ (max k₀ ⌈R⌉₊ : ℕ)).trans hr1), fun z hz => ?_⟩
  obtain ⟨hN, -, -⟩ := hr z hz
  have hr0 : 0 ≤ r := by rw [← hz]; exact norm_nonneg _
  have hx : 1 ≤ 1 + r := by linarith
  have hx0 : 0 < 1 + r := by linarith
  rw [hz] at hN
  have hen := airyEnv_pos z
  set A : ℝ := c * (1 + r) ^ (-(1 / 2 : ℝ)) * airyEnv z with hA
  have hApos : 0 < A := by positivity
  have hprod : ‖at47_pr S z‖ ≤ ((1 + T) * (1 + r)) ^ m := by
    unfold at47_pr
    rw [norm_prod]
    calc ∏ t ∈ S, ‖z - (t : ℂ)‖ ≤ ∏ t ∈ S, ((1 + T) * (1 + r)) := by
          gcongr with t ht
          have h1 : |t| ≤ T := Finset.single_le_sum (f := fun t => |t|) (fun _ _ => abs_nonneg _) ht
          have := norm_sub_le z (t : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs, hz] at this
          nlinarith
      _ = _ := by simp [m]
  have h1 : ‖G z‖ * A ≤ C * (1 + r) ^ ν * airyEnv z * ((1 + T) * (1 + r)) ^ m := by
    have e := congrArg norm (hG z)
    rw [norm_mul, norm_mul, norm_pow] at e
    calc ‖G z‖ * A ≤ ‖G z‖ * ‖airyPQN P Q z‖ ^ 2 := by gcongr
      _ = ‖f z‖ * ‖at47_pr S z‖ := e.symm
      _ ≤ (C * (1 + r) ^ ν * airyEnv z) * ((1 + T) * (1 + r)) ^ m := by
          have := hb z; rw [hz] at this
          gcongr
  have h2 : ‖G z‖ ≤ C * (1 + T) ^ m * (1 + r) ^ (ν + m + 1 / 2 : ℝ) / c := by
    have hexp : (1 + r) ^ (ν + m + 1 / 2 : ℝ) = (1 + r) ^ ν * (1 + r) ^ m * (1 + r) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_natCast]
    have hY : (1 + r) ^ (1 / 2 : ℝ) * (1 + r) ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← Real.rpow_add hx0]; norm_num
    have e1 : C * (1 + r) ^ ν * airyEnv z * ((1 + T) * (1 + r)) ^ m =
        (C * (1 + T) ^ m * (1 + r) ^ (ν + m + 1 / 2 : ℝ) / c) * A := by
      rw [hexp, hA, mul_pow]
      have : C * (1 + T) ^ m * ((1 + r) ^ ν * (1 + r) ^ m * (1 + r) ^ (1 / 2 : ℝ)) / c *
          (c * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv z) =
          C * (1 + r) ^ ν * airyEnv z * ((1 + T) ^ m * (1 + r) ^ m) *
            ((1 + r) ^ (1 / 2 : ℝ) * (1 + r) ^ (-(1 / 2) : ℝ)) := by
        field_simp
      rw [this, hY, mul_one]
    rw [e1] at h1
    exact le_of_mul_le_mul_right h1 hApos
  calc ‖G z‖ ≤ C * (1 + T) ^ m * (1 + r) ^ (ν + m + 1 / 2 : ℝ) / c := h2
    _ ≤ C * (1 + T) ^ m * (1 + r) ^ ⌈ν + m + 1 / 2⌉₊ / c := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil _)
    _ = _ := by ring

lemma at47_deriv2_mul_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {a : ℂ}
    (hfa : f a = 0) (hf'a : deriv f a = 0) (hga : g a = 0) : deriv (deriv (fun z => f z * g z)) a = 0 := by
  have hf' : Differentiable ℂ (deriv f) := hf.deriv
  have hg' : Differentiable ℂ (deriv g) := hg.deriv
  have e1 : deriv (fun z => f z * g z) = fun z => deriv f z * g z + f z * deriv g z := by
    funext z; exact deriv_mul (hf z) (hg z)
  rw [e1]
  have d1 : DifferentiableAt ℂ (fun z => deriv f z * g z) a := (hf' a).mul (hg a)
  have d2 : DifferentiableAt ℂ (fun z => f z * deriv g z) a := (hf a).mul (hg' a)
  have h1 : deriv (fun z => deriv f z * g z) a = deriv (deriv f) a * g a + deriv f a * deriv g a :=
    deriv_mul (hf' a) (hg a)
  have h2 : deriv (fun z => f z * deriv g z) a = deriv f a * deriv g a + f a * deriv (deriv g) a :=
    deriv_mul (hf a) (hg' a)
  have h3 : deriv (fun z => deriv f z * g z + f z * deriv g z) a =
      deriv (fun z => deriv f z * g z) a + deriv (fun z => f z * deriv g z) a := deriv_add d1 d2
  rw [h3, h1, h2, hfa, hf'a, hga]; simp

lemma at47_deriv2_sq {N : ℂ → ℂ} (hN : Differentiable ℂ N) {a : ℂ} (hNa : N a = 0) :
    deriv (deriv (fun z => N z ^ 2)) a = 2 * deriv N a ^ 2 := by
  have hN' : Differentiable ℂ (deriv N) := hN.deriv
  have e1 : deriv (fun z => N z ^ 2) = fun z => N z * deriv N z + N z * deriv N z := by
    funext z
    have e : (fun z => N z ^ 2) = fun z => N z * N z := by funext w; ring
    rw [e]
    have : deriv (fun z => N z * N z) z = deriv N z * N z + N z * deriv N z := deriv_mul (hN z) (hN z)
    rw [this]; ring
  rw [e1]
  have d1 : DifferentiableAt ℂ (fun z => N z * deriv N z) a := (hN a).mul (hN' a)
  have h1 : deriv (fun z => N z * deriv N z) a = deriv N a * deriv N a + N a * deriv (deriv N) a :=
    deriv_mul (hN a) (hN' a)
  have h3 : deriv (fun z => N z * deriv N z + N z * deriv N z) a =
      deriv (fun z => N z * deriv N z) a + deriv (fun z => N z * deriv N z) a := deriv_add d1 d1
  rw [h3, h1, hNa]; simp; ring

/-- **Theorem 4.7, uniqueness half** (`SOFT_EDGE_THEOREMS.md`).  `S` is the set of the `m = max (2 deg P + 1) (2 deg Q + 2)` largest
zeros of `N = P Ai + Q Ai'` (`hSz`, `hS_top`: every zero of `N` outside `S` lies below all of `S`), `tm = min S`.  If `f` is entire in the
class of `airyPQ_hasSum_unc`, real on `ℝ`, `∫ f ≤ 0`, `f ≥ 0` on `S` and on `(-∞, um]` with `um ≥ tm`, then
`f(z) ∏_{t ∈ S}(z - t) = c (-1)^m N(z)²` with a constant `c ≥ 0`, and `c = 0` if `um > tm`.  (So `f = c (-1)^m N²/∏(u - t_j)` off `S`,
and `f = 0` if `um > tm`.)  `S` is a hypothesis (it exists by `at47_top_zeros_min`); an ordered
enumeration `t_1 > ⋯ > t_m` as a function is not formalised. -/
theorem at47_uniqueness {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (S : Finset ℝ)
    (hcard : S.card = at47_m P Q) (hSz : ∀ t ∈ S, airyPQN P Q (t : ℂ) = 0)
    (hS_top : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t)
    {tm : ℝ} (htm : tm ∈ S) (hmin : ∀ t ∈ S, tm ≤ t) {um : ℝ} (hum : tm ≤ um)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hint : (∫ x : ℝ, f (x : ℂ)).re ≤ 0)
    (hfS : ∀ t ∈ S, 0 ≤ (f (t : ℂ)).re) (hfneg : ∀ x : ℝ, x ≤ um → 0 ≤ (f (x : ℂ)).re) :
    ∃ c : ℝ, 0 ≤ c ∧ (∀ z : ℂ, f z * at47_pr S z = ((c * (-1) ^ S.card : ℝ) : ℂ) * airyPQN P Q z ^ 2) ∧
      (tm < um → c = 0) := by
  classical
  have hnnN : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → 0 ≤ (f (x : ℂ)).re := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact hfS x hxS
    · exact hfneg x ((hS_top x hx hxS tm htm).le.trans hum)
  have hz0 := airyPQ_nonneg_zeros_vanish hHB hQ hf hfi hC hb hreal hnnN hint
  have hf'0 : ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x < um → deriv f (x : ℂ) = 0 := fun x hx hxu =>
    at47_deriv_eq_zero_of_min hf hreal hxu hfneg (hz0 x hx)
  set φ : ℂ → ℂ := fun z => f z * at47_pr S z with hφdef
  have hφ : Differentiable ℂ φ := hf.mul (at47_pr_differentiable S)
  have hzφ : ∀ z, airyPQN P Q z = 0 → φ z = 0 ∧ deriv φ z = 0 ∧ deriv (airyPQN P Q) z ≠ 0 := by
    intro z hz
    have hzr := airyPQ_zero_eq_ofReal hHB hz
    set x : ℝ := z.re with hx
    rw [hzr] at hz ⊢
    have hfx := hz0 x hz
    have hderiv : deriv φ (x : ℂ) = deriv f (x : ℂ) * at47_pr S (x : ℂ) + f (x : ℂ) * deriv (at47_pr S) (x : ℂ) :=
      deriv_mul (hf _) (at47_pr_differentiable S _)
    refine ⟨by simp [hφdef, hfx], ?_, ?_⟩
    · rw [hderiv, hfx]
      by_cases hxS : x ∈ S
      · rw [at47_pr_eq_zero hxS]; simp
      · have hxu : x < um := lt_of_lt_of_le (hS_top x hz hxS tm htm) hum
        rw [hf'0 x hz hxu]; simp
    · rw [deriv_airyPQN]; exact airyPQ_simple_of_HB hHB hQ _ hz
  obtain ⟨G, hG, hGe⟩ := EntireDiv.entire_exists_div_sq hφ (differentiable_airyPQN P Q) hzφ
  have hGe' : ∀ z, f z * at47_pr S z = G z * airyPQN P Q z ^ 2 := hGe
  obtain ⟨n, C', hC', hcirc⟩ := at47_G_circle_bound hQ S hC hb hGe'
  obtain ⟨p, -, hpe⟩ := at47_entire_polynomial_of_circle_bound n hG hC' hcirc
  have hpdeg : p.natDegree = 0 := by
    by_contra hne
    have hp1 : 1 ≤ p.natDegree := Nat.one_le_iff_ne_zero.mpr hne
    refine at47_not_integrable_poly_mul P Q hQ S hcard p hp1 ?_
    have hae : ∀ᵐ x : ℝ ∂volume, x ∉ (S : Set ℝ) := by
      rw [ae_iff]; simpa using S.finite_toSet.measure_zero volume
    refine hfi.congr ?_
    filter_upwards [hae] with x hx
    have hxS : x ∉ S := by simpa using hx
    have h := hGe' (x : ℂ)
    rw [hpe (x : ℂ)] at h
    have hpr := at47_pr_ne_zero hxS
    have hN : airyPQN P Q (x : ℂ) = ((at47_Nf P Q x : ℝ) : ℂ) := airyPQN_ofReal P Q x
    rw [hN] at h
    rw [eq_div_iff (by simpa [at47_pr] using hpr)]
    simpa [at47_pr] using h
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z, p.eval z = c :=
    ⟨p.coeff 0, fun z => by rw [Polynomial.eq_C_of_natDegree_eq_zero hpdeg]; simp⟩
  have hfc : ∀ z, f z * at47_pr S z = c * airyPQN P Q z ^ 2 := fun z => by rw [hGe' z, hpe z, hc z]
  -- c is real
  obtain ⟨x0, -, hx0⟩ := at47_exists_real_ne_zero hHB 0
  have hN0 : airyPQN P Q (x0 : ℂ) = ((at47_Nf P Q x0 : ℝ) : ℂ) := airyPQN_ofReal P Q x0
  have hNr0 : at47_Nf P Q x0 ≠ 0 := by
    intro h; apply hx0; rw [hN0, h]; simp
  have hcim : c.im = 0 := by
    have e := congrArg Complex.im (hfc (x0 : ℂ))
    rw [at47_pr_ofReal, hN0, ← Complex.ofReal_pow, Complex.im_mul_ofReal, Complex.im_mul_ofReal, hreal] at e
    simp at e
    rcases e with e | e
    · exact e
    · exact absurd e hNr0
  have hcre : c = (c.re : ℂ) := Complex.ext (by simp) (by simp [hcim])
  -- c ≥ 0 after the sign
  obtain ⟨x1, hx1lt, hx1⟩ := at47_exists_real_ne_zero hHB tm
  have hN1 : airyPQN P Q (x1 : ℂ) = ((at47_Nf P Q x1 : ℝ) : ℂ) := airyPQN_ofReal P Q x1
  have hNr1 : at47_Nf P Q x1 ≠ 0 := by
    intro h; apply hx1; rw [hN1, h]; simp
  have hfx1 : f (x1 : ℂ) = (((f (x1 : ℂ)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hreal x1])
  have hreal_eq : (f (x1 : ℂ)).re * (∏ t ∈ S, (x1 - t)) = c.re * at47_Nf P Q x1 ^ 2 := by
    have e := hfc (x1 : ℂ)
    rw [at47_pr_ofReal, hN1, hcre, hfx1] at e
    have e' : (((f (x1 : ℂ)).re * (∏ t ∈ S, (x1 - t)) : ℝ) : ℂ) = ((c.re * at47_Nf P Q x1 ^ 2 : ℝ) : ℂ) := by
      push_cast; push_cast at e; exact e
    exact_mod_cast e'
  have hcnn : 0 ≤ c.re * (-1) ^ S.card := by
    have hs := at47_pr_sign (S := S) (x := x1) (fun t ht => (hx1lt.trans_le (hmin t ht)).le)
    have hf1 := hfneg x1 (by linarith)
    have hNsq : 0 < at47_Nf P Q x1 ^ 2 := by positivity
    have : (c.re * (-1) ^ S.card) * at47_Nf P Q x1 ^ 2 =
        (f (x1 : ℂ)).re * ((-1) ^ S.card * ∏ t ∈ S, (x1 - t)) := by
      calc (c.re * (-1) ^ S.card) * at47_Nf P Q x1 ^ 2 = (-1) ^ S.card * (c.re * at47_Nf P Q x1 ^ 2) := by ring
        _ = (-1) ^ S.card * ((f (x1 : ℂ)).re * ∏ t ∈ S, (x1 - t)) := by rw [← hreal_eq]
        _ = _ := by ring
    have h2 : 0 ≤ (c.re * (-1) ^ S.card) * at47_Nf P Q x1 ^ 2 := by rw [this]; positivity
    exact nonneg_of_mul_nonneg_left h2 hNsq
  refine ⟨c.re * (-1) ^ S.card, hcnn, fun z => ?_, fun hlt => ?_⟩
  · rw [hfc z, hcre]
    have h1 : ((-1 : ℂ) ^ S.card) * (-1) ^ S.card = 1 := by rw [← mul_pow]; simp
    push_cast
    linear_combination (-((c.re : ℂ) * airyPQN P Q z ^ 2)) * h1
  · have hN := differentiable_airyPQN P Q
    have hfa : f (tm : ℂ) = 0 := hz0 tm (hSz tm htm)
    have hf'a : deriv f (tm : ℂ) = 0 := hf'0 tm (hSz tm htm) hlt
    have hpr : at47_pr S (tm : ℂ) = 0 := at47_pr_eq_zero htm
    have h1 := at47_deriv2_mul_zero hf (at47_pr_differentiable S) hfa hf'a hpr
    have e : (fun z => f z * at47_pr S z) = fun z => c * airyPQN P Q z ^ 2 := funext hfc
    rw [e] at h1
    have hd1 : Differentiable ℂ (fun z => airyPQN P Q z ^ 2) := by fun_prop
    have e2 : deriv (fun z => c * airyPQN P Q z ^ 2) = fun z => c * deriv (fun z => airyPQN P Q z ^ 2) z := by
      funext z; exact deriv_const_mul c (hd1 z)
    rw [e2, deriv_const_mul c (hd1.deriv (tm : ℂ))] at h1
    rw [at47_deriv2_sq hN (hSz tm htm)] at h1
    have hne : deriv (airyPQN P Q) (tm : ℂ) ≠ 0 := by
      rw [deriv_airyPQN]; exact airyPQ_simple_of_HB hHB hQ _ (hSz tm htm)
    have h2 : c = 0 := by
      have : c * (2 * deriv (airyPQN P Q) (tm : ℂ) ^ 2) = 0 := h1
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exfalso; simp at h; exact hne h
    have : c.re = 0 := by rw [h2]; simp
    rw [this]; simp

/-- info: 'FormalResearch.Special.at47_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_uniqueness

end FormalResearch.Special
