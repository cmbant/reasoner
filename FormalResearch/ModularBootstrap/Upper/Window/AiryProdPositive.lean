module

public import FormalResearch.ModularBootstrap.Upper.Window.Product

/-!
# Sign structure of the Airy window product (`ut:R`, Lemma R, real-zero part)

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, proof of Lemma R (`ut:R`): the real entire Airy
product `W^{(f)}(u) = -Ai(u)² (u - u_f) ∏_{k>f}((u-u_k)² + ε_k²) / ∏_{k≥1}(u - a_k)²`
(`airyWindowProd`) has exactly one real zero, simple, at `u_f`, because the double zeros of `Ai²` at
`a_k` are cancelled by the poles of the product, the factors `(u - u_k)² + ε_k²` are positive when
`ε_k ≠ 0`, and `u - u_f` changes sign once.  `W < 0` on the lobe `u > u_f` and `W > 0` on the band `u < u_f`.

* `real_tprod_pos`: a product of positive reals with `∑ |p_m - 1| < ∞` is positive.
* `airyProdTail_real_pos`, `airyProdTailExcept_real_pos`: at a real point away from the Airy zeros the
  tails `airyProdTail`, `airyProdTailExcept` are positive real numbers.
* `airyWindowProd_re_pos`, `airyWindowProd_re_neg`, `airyWindowProd_re_zero`: the sign of `Re W^{(f)}` on
  `u < u_f`, `u > u_f`, `u = u_f`, under `ε_k ≠ 0` for all `k > f`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Window

open FormalResearch.Special

/-! ### Positive products -/

/-- A product of positive reals with summable `|p_m - 1|` is positive and is the sum-of-logs
exponential. -/
lemma real_tprod_pos {p : ℕ → ℝ} (hp : ∀ m, 0 < p m) (hs : Summable fun m => |p m - 1|) :
    HasProd p (∏' m, p m) ∧ 0 < ∏' m, p m := by
  have hlog : Summable fun m => Real.log (p m) := by
    have h1 : Summable fun m => p m - 1 := hs.of_abs
    simpa using Real.summable_log_one_add_of_summable h1
  refine ⟨(Real.multipliable_of_summable_log hp hlog).hasProd, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hp hlog]
  exact Real.exp_pos _

/-- The real value of a single window factor. -/
lemma airyProdFactor_ofReal (uSite epsU : ℕ → ℝ) (k : ℕ) (u : ℝ) :
    airyProdFactor uSite epsU k (u : ℂ) =
      ((((u - uSite k) ^ 2 + epsU k ^ 2) / (u - airyZero k) ^ 2 : ℝ) : ℂ) := by
  unfold airyProdFactor
  push_cast
  ring

lemma realFactor_sub_one_le {u a s e : ℝ} (hua : u ≠ a) :
    |((u - s) ^ 2 + e ^ 2) / (u - a) ^ 2 - 1| ≤
      2 * |a - s| / |u - a| + (|a - s| ^ 2 + |e| ^ 2) / |u - a| ^ 2 := by
  have hne : u - a ≠ 0 := sub_ne_zero.mpr hua
  have hpos : 0 < |u - a| := abs_pos.mpr hne
  have heq : ((u - s) ^ 2 + e ^ 2) / (u - a) ^ 2 - 1 =
      2 * (a - s) / (u - a) + ((a - s) ^ 2 + e ^ 2) / (u - a) ^ 2 := by
    field_simp
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_mul, abs_two]
  · refine le_of_eq ?_
    rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (a - s) ^ 2 + e ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ (u - a) ^ 2)]
    simp only [sq_abs]

/-- Summability of `|p_m - 1|` for the window factors at a real point, with skipped indices. -/
lemma summable_abs_factor_sub_one (f : ℕ) (uSite epsU : ℕ → ℝ)
    (hH : AiryProdTailHypothesis f uSite epsU) (u : ℝ) (skip : ℕ → Prop) [DecidablePred skip]
    (hne : ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ airyZero (f + 1 + m)) :
    Summable fun m : ℕ => |(if skip (f + 1 + m) then (1 : ℝ) else
      ((u - uSite (f + 1 + m)) ^ 2 + epsU (f + 1 + m) ^ 2) / (u - airyZero (f + 1 + m)) ^ 2) - 1| := by
  obtain ⟨K₀, _, hK₀⟩ := norm_sub_airyZero_ge_eventually (|u|)
  obtain ⟨C_H, hC_H, hH_bd⟩ := hH
  obtain ⟨C_Z, hC_Z, hZ_bd⟩ := deltaWKB_le_exists
  set M_H := C_H + C_Z
  have hM_H : 0 < M_H := by positivity
  set C_maj : ℝ := 2 * M_H + (M_H ^ 2 + C_H ^ 2)
  have hsum_maj : Summable (fun m : ℕ => C_maj * (((f + 1 + m + K₀ : ℕ) : ℝ) ^ (-2 : ℝ))) := by
    have h2 : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
      simpa using this
    refine (h2.mul_left C_maj).of_nonneg_of_le (fun _ => by positivity) fun m => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
    exact_mod_cast (by omega : m + 1 ≤ f + 1 + m + K₀)
  refine (summable_nat_add_iff K₀).mp (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hsum_maj)
  set k := f + 1 + (m + K₀) with hk
  have hk' : f + 1 + m + K₀ = k := by omega
  rw [hk']
  by_cases hskip : skip k
  · simp only [hskip, ↓reduceIte, sub_self, abs_zero]
    positivity
  · simp only [hskip, ↓reduceIte]
    have hkm : K₀ ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hfk : f < k := by omega
    have hdist' := hK₀ k hkm (u : ℂ) (by simp)
    have hdist : (k : ℝ) ^ (2 / 3 : ℝ) ≤ |u - airyZero k| := by
      have h3 : ‖(u : ℂ) - (airyZero k : ℂ)‖ = |u - airyZero k| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rwa [h3] at hdist'
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk1
    have hu_ne : u ≠ airyZero k := hne (m + K₀) hskip
    have hnorm := realFactor_sub_one_le (s := uSite k) (e := epsU k) hu_ne
    obtain ⟨h_u, h_e⟩ := hH_bd k hfk
    have h_δ := hZ_bd k hk1
    have h_diff : |airyZero k - uSite k| ≤ M_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
      have htri : |airyZero k - uSite k| ≤ |airyZero k - uWKB k| + |uSite k - uWKB k| := by
        have : airyZero k - uSite k = (airyZero k - uWKB k) - (uSite k - uWKB k) := by ring
        rw [this]; exact abs_sub _ _
      have h_δ' : |airyZero k - uWKB k| ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) := h_δ
      calc |airyZero k - uSite k|
          ≤ |airyZero k - uWKB k| + |uSite k - uWKB k| := htri
        _ ≤ C_Z * (k : ℝ) ^ (-(4 / 3 : ℝ)) + C_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := add_le_add h_δ' h_u
        _ = M_H * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by dsimp [M_H]; ring
    have hdpos : 0 < (k : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk_pos _
    have h1 : 2 * |airyZero k - uSite k| / |u - airyZero k| ≤ 2 * M_H * (k : ℝ) ^ (-2 : ℝ) := by
      calc 2 * |airyZero k - uSite k| / |u - airyZero k|
          ≤ 2 * (M_H * (k : ℝ) ^ (-(4 / 3 : ℝ))) / (k : ℝ) ^ (2 / 3 : ℝ) := by gcongr
        _ = 2 * M_H * ((k : ℝ) ^ (-(4 / 3 : ℝ)) / (k : ℝ) ^ (2 / 3 : ℝ)) := by ring
        _ = 2 * M_H * (k : ℝ) ^ (-2 : ℝ) := by
            rw [← Real.rpow_sub hk_pos]
            congr 2; norm_num
    have hsq_diff : |airyZero k - uSite k| ^ 2 ≤ M_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have h1' := pow_le_pow_left₀ (abs_nonneg _) h_diff 2
      rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(4 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
        show -(4 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(8 / 3 : ℝ) by norm_num] at h1'
      refine h1'.trans ?_
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk1' (by norm_num)) (by positivity)
    have hsq_eps : |epsU k| ^ 2 ≤ C_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) := by
      have h1' := pow_le_pow_left₀ (abs_nonneg _) h_e 2
      rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hk_pos.le,
        show -(1 / 3 : ℝ) * ((2 : ℕ) : ℝ) = -(2 / 3 : ℝ) by norm_num] at h1'
      exact h1'
    have h2 : (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / |u - airyZero k| ^ 2 ≤
        (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) := by
      have hdist2 : (k : ℝ) ^ (4 / 3 : ℝ) ≤ |u - airyZero k| ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hdist 2
        rwa [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le,
          show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 3 by norm_num] at this
      calc (|airyZero k - uSite k| ^ 2 + |epsU k| ^ 2) / |u - airyZero k| ^ 2
          ≤ (M_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ)) + C_H ^ 2 * (k : ℝ) ^ (-(2 / 3 : ℝ))) /
              (k : ℝ) ^ (4 / 3 : ℝ) := by gcongr
        _ = (M_H ^ 2 + C_H ^ 2) * ((k : ℝ) ^ (-(2 / 3 : ℝ)) / (k : ℝ) ^ (4 / 3 : ℝ)) := by ring
        _ = (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) := by
            rw [← Real.rpow_sub hk_pos]; congr 2; norm_num
    calc _ ≤ _ := hnorm
      _ ≤ 2 * M_H * (k : ℝ) ^ (-2 : ℝ) + (M_H ^ 2 + C_H ^ 2) * (k : ℝ) ^ (-2 : ℝ) := add_le_add h1 h2
      _ = C_maj * (k : ℝ) ^ (-2 : ℝ) := by dsimp [C_maj]; ring

/-- A complex `HasProd` of window factors (with skipped indices) at a real point is a positive real. -/
lemma hasProd_skip_real_pos {f : ℕ} {uSite epsU : ℕ → ℝ} (hH : AiryProdTailHypothesis f uSite epsU)
    {u : ℝ} (skip : ℕ → Prop) [DecidablePred skip]
    (hne : ∀ m : ℕ, ¬skip (f + 1 + m) → u ≠ airyZero (f + 1 + m))
    (hε : ∀ m : ℕ, ¬skip (f + 1 + m) → epsU (f + 1 + m) ≠ 0) {Pc : ℂ}
    (hP : HasProd (fun m : ℕ => if skip (f + 1 + m) then (1 : ℂ) else
      airyProdFactor uSite epsU (f + 1 + m) (u : ℂ)) Pc) :
    ∃ P : ℝ, 0 < P ∧ Pc = (P : ℂ) := by
  set p : ℕ → ℝ := fun m => if skip (f + 1 + m) then (1 : ℝ) else
    ((u - uSite (f + 1 + m)) ^ 2 + epsU (f + 1 + m) ^ 2) / (u - airyZero (f + 1 + m)) ^ 2 with hpdef
  have hp : ∀ m, 0 < p m := by
    intro m
    by_cases hs : skip (f + 1 + m)
    · simp only [hpdef, hs, ↓reduceIte, zero_lt_one]
    · simp only [hpdef, hs, ↓reduceIte]
      have h1 : 0 < epsU (f + 1 + m) ^ 2 := by
        have := hε m hs
        positivity
      have h2 : 0 < (u - airyZero (f + 1 + m)) ^ 2 := by
        have := sub_ne_zero.mpr (hne m hs)
        positivity
      have h3 := sq_nonneg (u - uSite (f + 1 + m))
      positivity
  obtain ⟨hpr, hpos⟩ := real_tprod_pos hp (summable_abs_factor_sub_one f uSite epsU hH u skip hne)
  refine ⟨∏' m, p m, hpos, ?_⟩
  have hmap := hpr.map (Complex.ofRealHom : ℝ →* ℂ) Complex.continuous_ofReal
  have hfun : ((Complex.ofRealHom : ℝ →* ℂ) ∘ p) = fun m : ℕ => if skip (f + 1 + m) then (1 : ℂ) else
      airyProdFactor uSite epsU (f + 1 + m) (u : ℂ) := by
    funext m
    by_cases hs : skip (f + 1 + m)
    · simp [hpdef, hs]
    · simp [hpdef, hs, airyProdFactor_ofReal]
  rw [hfun] at hmap
  exact hP.unique hmap

/-- At a real point away from the Airy zeros, the tail `airyProdTail` is a positive real, provided no
width vanishes. -/
lemma airyProdTail_real_pos {f : ℕ} {uSite epsU : ℕ → ℝ} (hH : AiryProdTailHypothesis f uSite epsU)
    {u : ℝ} (hne : ∀ k : ℕ, f < k → u ≠ airyZero k) (hε : ∀ k : ℕ, f < k → epsU k ≠ 0) :
    ∃ P : ℝ, 0 < P ∧ airyProdTail f uSite epsU (u : ℂ) = (P : ℂ) := by
  have hne' : ∀ k : ℕ, f < k → (u : ℂ) ≠ (airyZero k : ℂ) := fun k hk h =>
    hne k hk (Complex.ofReal_injective h)
  have hP := hasProd_airyProdTail hH hne'
  exact hasProd_skip_real_pos hH (fun _ => False) (fun m _ => hne _ (by omega))
    (fun m _ => hε _ (by omega)) (by simpa using hP)

/-- The tail omitting the index `n` at a real point avoiding the other Airy zeros. -/
lemma airyProdTailExcept_real_pos {f n : ℕ} {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) {u : ℝ}
    (hne : ∀ k : ℕ, f < k → k ≠ n → u ≠ airyZero k) (hε : ∀ k : ℕ, f < k → k ≠ n → epsU k ≠ 0) :
    ∃ P : ℝ, 0 < P ∧ airyProdTailExcept f n uSite epsU (u : ℂ) = (P : ℂ) := by
  have hne' : ∀ k : ℕ, f < k → k ≠ n → (u : ℂ) ≠ (airyZero k : ℂ) := fun k hk hkn h =>
    hne k hk hkn (Complex.ofReal_injective h)
  have hP := hasProd_airyProdTailExcept (n := n) hH hne'
  exact hasProd_skip_real_pos hH (fun k => k = n) (fun m hm => hne _ (by omega) hm)
    (fun m hm => hε _ (by omega) hm) hP

/-! ### The sign of the window product on the real line -/

lemma airyZero_ne_of_ne {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : m ≠ n) : airyZero m ≠ airyZero n :=
  fun e => h (airyZero_injective_on hm hn e)

/-- On the real line, `W^{(f)}(u) = -(u - u_f) S(u)` with `S(u) > 0`: the product has the single simple
real zero `u_f`, is positive on `u < u_f` and negative on `u > u_f`.  Requires `ε_k ≠ 0` for `k > f`. -/
theorem airyWindowProd_eq_neg_mul_pos {f : ℕ} (uF : ℝ) {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) (hε : ∀ k : ℕ, f < k → epsU k ≠ 0) (u : ℝ) :
    ∃ S : ℝ, 0 < S ∧ airyWindowProd f uF uSite epsU (u : ℂ) = ((-(u - uF) * S : ℝ) : ℂ) := by
  by_cases hz : ∃ n : ℕ, 1 ≤ n ∧ u = airyZero n
  · obtain ⟨n, hn, rfl⟩ := hz
    have hderiv : airyAi' (airyZero n) ≠ 0 := fun h0 =>
      airyAi_ne_zero_of_deriv_zero h0 (airyAi_airyZero n)
    by_cases hnf : n ≤ f
    · rw [airyWindowProd_at_airyZero_le f uF uSite epsU hn hnf, deriv_airyAiC_ofReal]
      obtain ⟨P, hP, hPe⟩ := airyProdTail_real_pos hH (u := airyZero n)
        (fun k hk h => airyZero_ne_of_ne hn (by omega) (by omega) h) hε
      rw [hPe]
      have hden : 0 < ∏ k ∈ (Finset.Icc 1 f).erase n, (airyZero n - airyZero k) ^ 2 :=
        Finset.prod_pos fun k hk => by
          have hk' := Finset.mem_erase.mp hk
          have hk2 := Finset.mem_Icc.mp hk'.2
          have := sub_ne_zero.mpr (airyZero_ne_of_ne hn hk2.1 (Ne.symm hk'.1))
          positivity
      refine ⟨airyAi' (airyZero n) ^ 2 / (∏ k ∈ (Finset.Icc 1 f).erase n,
        (airyZero n - airyZero k) ^ 2) * P, by positivity, ?_⟩
      push_cast
      ring
    · have hfn : f < n := by omega
      rw [airyWindowProd_at_airyZero_gt f uF uSite epsU hfn, deriv_airyAiC_ofReal]
      obtain ⟨P, hP, hPe⟩ := airyProdTailExcept_real_pos (n := n) hH (u := airyZero n)
        (fun k hk hkn h => airyZero_ne_of_ne hn (by omega) (Ne.symm hkn) h)
        (fun k hk _ => hε k hk)
      rw [hPe]
      have hden : 0 < ∏ k ∈ Finset.Icc 1 f, (airyZero n - airyZero k) ^ 2 :=
        Finset.prod_pos fun k hk => by
          have hk2 := Finset.mem_Icc.mp hk
          have := sub_ne_zero.mpr (airyZero_ne_of_ne hn hk2.1 (by omega))
          positivity
      have hnum : 0 < (airyZero n - uSite n) ^ 2 + epsU n ^ 2 := by
        have := hε n hfn
        positivity
      refine ⟨airyAi' (airyZero n) ^ 2 / (∏ k ∈ Finset.Icc 1 f, (airyZero n - airyZero k) ^ 2) *
        ((airyZero n - uSite n) ^ 2 + epsU n ^ 2) * P, by positivity, ?_⟩
      push_cast
      ring
  · push Not at hz
    have hu : ∀ n : ℕ, 1 ≤ n → (u : ℂ) ≠ (airyZero n : ℂ) := fun n hn h =>
      hz n hn (Complex.ofReal_injective h)
    rw [airyWindowProd_eq_of_ne f uF uSite epsU hu, airyAiC_ofReal]
    obtain ⟨P, hP, hPe⟩ := airyProdTail_real_pos hH (u := u)
      (fun k hk h => hz k (by omega) h) hε
    rw [hPe]
    have hAi : airyAi u ≠ 0 := by
      intro h0
      rcases le_or_gt 0 u with hu0 | hu0
      · exact airyAi_ne_zero_of_nonneg hu0 h0
      · obtain ⟨n, hn, hun⟩ := exists_airyZero_eq h0 hu0.le
        exact hz n hn hun
    have hden : 0 < ∏ k ∈ Finset.Icc 1 f, (u - airyZero k) ^ 2 :=
      Finset.prod_pos fun k hk => by
        have hk2 := Finset.mem_Icc.mp hk
        have := sub_ne_zero.mpr (hz k hk2.1)
        positivity
    refine ⟨airyAi u ^ 2 / (∏ k ∈ Finset.Icc 1 f, (u - airyZero k) ^ 2) * P, by positivity, ?_⟩
    push_cast
    ring

/-- `Re W^{(f)}(u) > 0` on the band `u < u_f`. -/
theorem airyWindowProd_re_pos {f : ℕ} (uF : ℝ) {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) (hε : ∀ k : ℕ, f < k → epsU k ≠ 0) {u : ℝ}
    (hu : u < uF) : 0 < (airyWindowProd f uF uSite epsU (u : ℂ)).re := by
  obtain ⟨S, hS, h⟩ := airyWindowProd_eq_neg_mul_pos uF hH hε u
  rw [h, Complex.ofReal_re]
  have : 0 < uF - u := sub_pos.mpr hu
  nlinarith

/-- `Re W^{(f)}(u) < 0` on the lobe `u > u_f`. -/
theorem airyWindowProd_re_neg {f : ℕ} (uF : ℝ) {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) (hε : ∀ k : ℕ, f < k → epsU k ≠ 0) {u : ℝ}
    (hu : uF < u) : (airyWindowProd f uF uSite epsU (u : ℂ)).re < 0 := by
  obtain ⟨S, hS, h⟩ := airyWindowProd_eq_neg_mul_pos uF hH hε u
  rw [h, Complex.ofReal_re]
  have : 0 < u - uF := sub_pos.mpr hu
  nlinarith

/-- The only real zero of `W^{(f)}` is `u_f`. -/
theorem airyWindowProd_re_eq_zero_iff {f : ℕ} (uF : ℝ) {uSite epsU : ℕ → ℝ}
    (hH : AiryProdTailHypothesis f uSite epsU) (hε : ∀ k : ℕ, f < k → epsU k ≠ 0) (u : ℝ) :
    (airyWindowProd f uF uSite epsU (u : ℂ)).re = 0 ↔ u = uF := by
  obtain ⟨S, hS, h⟩ := airyWindowProd_eq_neg_mul_pos uF hH hε u
  rw [h, Complex.ofReal_re]
  constructor
  · intro h0
    have := mul_eq_zero.mp h0
    rcases this with h1 | h1
    · linarith
    · exact absurd h1 hS.ne'
  · intro h0
    rw [h0]; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.airyWindowProd_eq_neg_mul_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyWindowProd_eq_neg_mul_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.airyWindowProd_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyWindowProd_re_pos

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.airyWindowProd_re_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyWindowProd_re_neg

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.airyWindowProd_re_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyWindowProd_re_eq_zero_iff

end FormalResearch.ModularBootstrap.Upper.Window
