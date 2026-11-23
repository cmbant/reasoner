module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The near-pair sum of Proposition 1.2(2), Step 3 (iii) (`rem:P1.2`)

The four-range summation of `remainder.tex`, Proposition 1.2, proof of (2), Step 3 (iii): for sites `σ_k`
with the separation `σ_k - σ_j ≥ c_1 (k - j) k^{-1/3}` (`j < k`) and widths `ε_k ≤ C_0 k^{-1/3}`, the weights
`T_k = ε_k²/((s - σ_k)² + ε_k²)` satisfy `∑_{k ≥ 2} T_k (|s - σ_k| + 1) ≤ C`, uniformly in `s ∈ ℝ`, in the
sites and in the widths (`nearSum_le`).  The nearest site `k_*` replaces the case distinction `σ ≤ σ_1`.
-/

@[expose] public section

open Finset

namespace FormalResearch.ModularBootstrap.Upper.Ramped

/-- The weight `T = ε²/(d² + ε²)` of a near pair at signed distance `d` (`0` when `d = ε = 0`). -/
noncomputable def nearT (ε d : ℝ) : ℝ := ε ^ 2 / (d ^ 2 + ε ^ 2)

lemma nearT_nonneg (ε d : ℝ) : 0 ≤ nearT ε d := by unfold nearT; positivity

lemma nearT_le_one (ε d : ℝ) : nearT ε d ≤ 1 := by
  unfold nearT
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg d) (sq_nonneg ε)) with h | h
  · rw [← h]; simp
  · rw [div_le_one h]; nlinarith [sq_nonneg d]

lemma nearT_le_div {ε d : ℝ} (hd : d ≠ 0) : nearT ε d ≤ ε ^ 2 / d ^ 2 := by
  unfold nearT
  have hd2 : 0 < d ^ 2 := by positivity
  exact div_le_div_of_nonneg_left (sq_nonneg ε) hd2 (by nlinarith [sq_nonneg ε])

lemma nearT_mul_abs_le_div {ε d : ℝ} (hd : d ≠ 0) : nearT ε d * |d| ≤ ε ^ 2 / |d| := by
  have h1 := nearT_le_div (ε := ε) hd
  have hd' : 0 < |d| := abs_pos.mpr hd
  calc nearT ε d * |d| ≤ ε ^ 2 / d ^ 2 * |d| := by gcongr
    _ = ε ^ 2 / |d| := by
        rw [← sq_abs d]; field_simp

lemma nearT_mul_abs_le_half {ε d : ℝ} (hε : 0 ≤ ε) : nearT ε d * |d| ≤ ε / 2 := by
  unfold nearT
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg d) (sq_nonneg ε)) with h | h
  · rw [← h]; simp; positivity
  · rw [div_mul_eq_mul_div, div_le_iff₀ h]
    nlinarith [sq_nonneg (|d| - ε), sq_abs d, abs_nonneg d]

/-! ### Partial sums of `k^{-2/3}` -/

/-- `k^{-1/3}`. -/
noncomputable def cr (k : ℕ) : ℝ := (k : ℝ) ^ (-(1 / 3 : ℝ))

lemma cr_pos {k : ℕ} (hk : 1 ≤ k) : 0 < cr k := by
  unfold cr; exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _

lemma cr_le_one {k : ℕ} (hk : 1 ≤ k) : cr k ≤ 1 := by
  unfold cr
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by norm_num)

lemma cr_cube {k : ℕ} (hk : 1 ≤ k) : cr k ^ 3 = (k : ℝ)⁻¹ := by
  unfold cr
  have h0 : (0 : ℝ) ≤ k := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num [Real.rpow_neg_one]

lemma cr_anti {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) : cr k ≤ cr j := by
  unfold cr
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hj) (by exact_mod_cast hjk) (by norm_num)

/-- `∑_{k=1}^n k^{-2/3} ≤ 3 n^{1/3}`, in the form `∑ cr(k)² ≤ 3 / cr(n)`. -/
lemma sum_cr_sq_le (n : ℕ) (hn : 1 ≤ n) : ∑ k ∈ Icc 1 n, cr k ^ 2 ≤ 3 / cr n := by
  induction n, hn using Nat.le_induction with
  | base => simp [cr]
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    have h1 := cr_pos hn
    have h2 := cr_pos (by omega : 1 ≤ n + 1)
    have hc1 := cr_cube hn
    have hc2 := cr_cube (by omega : 1 ≤ n + 1)
    have hnn : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : cr (n + 1) ≤ cr n := cr_anti hn (by omega)
    -- `3/cr(n+1) - 3/cr n ≥ cr(n+1)^2`: with `a = 1/cr(n+1)`, `b = 1/cr n`, `a^3 - b^3 = 1`
    have hcast : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
    rw [hcast] at hc2
    set a := cr (n + 1)
    set b := cr n
    have hab : a ^ 3 * (n + 1) = 1 := by rw [hc2]; field_simp
    have hbb : b ^ 3 * n = 1 := by rw [hc1]; field_simp
    -- goal: S + a^2 ≤ 3/a, with S ≤ 3/b
    have key : a ^ 2 ≤ 3 / a - 3 / b := by
      rw [div_sub_div _ _ h2.ne' h1.ne', le_div_iff₀ (by positivity)]
      -- a^2 * (a*b) ≤ 3 b - 3 a ; i.e. a^3 b ≤ 3 (b - a)
      have hd3 : b ^ 3 - a ^ 3 = a ^ 3 * b ^ 3 := by linear_combination (-b ^ 3) * hab + a ^ 3 * hbb
      have hba : 0 ≤ b - a := by linarith
      have h4 : a ^ 3 * b ^ 3 ≤ 3 * b ^ 2 * (b - a) := by
        have : (b - a) * (b ^ 2 + a * b + a ^ 2) = a ^ 3 * b ^ 3 := by rw [← hd3]; ring
        rw [← this]
        have h5 : b ^ 2 + a * b + a ^ 2 ≤ 3 * b ^ 2 := by nlinarith [mul_nonneg h2.le hba]
        nlinarith [mul_le_mul_of_nonneg_left h5 hba]
      have h6 : a ^ 3 * b ≤ 3 * (b - a) := by
        have hb2 : 0 < b ^ 2 := by positivity
        by_contra hcon
        have hcon := lt_of_not_ge hcon
        have := mul_lt_mul_of_pos_left hcon hb2
        nlinarith [this, h4]
      nlinarith [h6]
    linarith

lemma cr_ge_inv {i : ℕ} (hi : 1 ≤ i) : (i : ℝ)⁻¹ ≤ cr i := by
  have h1 := cr_pos hi
  have h3 := cr_cube hi
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have : ((i : ℝ)⁻¹) ^ 3 ≤ cr i ^ 3 := by
    rw [h3]
    have h0 : (i : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hi1
    have h00 : 0 ≤ (i : ℝ)⁻¹ := by positivity
    calc ((i : ℝ)⁻¹) ^ 3 ≤ (i : ℝ)⁻¹ ^ 1 := pow_le_pow_of_le_one h00 h0 (by norm_num)
      _ = (i : ℝ)⁻¹ := pow_one _
  exact le_of_pow_le_pow_left₀ (by norm_num) h1.le this

/-- The kernel `i^{-4/3}`. -/
noncomputable def kern (i : ℕ) : ℝ := (i : ℝ)⁻¹ * cr i

lemma kern_nonneg (i : ℕ) : 0 ≤ kern i := by
  unfold kern cr; positivity

lemma kern_summable : Summable kern := by
  have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 4 / 3)
  refine h.congr fun i => ?_
  unfold kern cr
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
    have : (i : ℝ)⁻¹ * (i : ℝ) ^ (-(1 / 3 : ℝ)) = (i : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hi0]; norm_num
    rw [this, Real.rpow_neg hi0.le]

/-- The bound `Z`: partial sums of `kern` are at most `Z`. -/
noncomputable def kernZ : ℝ := ∑' i, kern i

lemma sum_kern_le (n : ℕ) : ∑ i ∈ Icc 1 n, kern i ≤ kernZ :=
  kern_summable.sum_le_tsum _ (fun i _ => kern_nonneg i)

lemma sum_kern_comp_le (S : Finset ℕ) (f : ℕ → ℕ) (hinj : Set.InjOn f S) :
    ∑ k ∈ S, kern (f k) ≤ kernZ := by
  rw [← Finset.sum_image hinj]
  exact kern_summable.sum_le_tsum _ (fun i _ => kern_nonneg i)

/-! ### The nearest site -/

lemma exists_nearest {c1 : ℝ} (hc1 : 0 < c1) (σ : ℕ → ℝ)
    (hsep : ∀ j k : ℕ, 1 ≤ j → j < k → c1 * (((k : ℝ) - j) * cr k) ≤ σ k - σ j) (s : ℝ) :
    ∃ ks : ℕ, 1 ≤ ks ∧ ∀ k : ℕ, 1 ≤ k → |s - σ ks| ≤ |s - σ k| := by
  have hlow : ∀ k : ℕ, 2 ≤ k → σ 1 + c1 * ((k : ℝ) ^ (2 / 3 : ℝ) - 1) ≤ σ k := by
    intro k hk
    have h := hsep 1 k le_rfl (by omega)
    norm_num at h
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkc : (k : ℝ) * cr k = (k : ℝ) ^ (2 / 3 : ℝ) := by
      unfold cr
      rw [show (k : ℝ) ^ (2 / 3 : ℝ) = (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ (-(1 / 3 : ℝ)) by
        rw [← Real.rpow_add hk0]; norm_num, Real.rpow_one]
    have hcr1 := cr_le_one (by omega : 1 ≤ k)
    have hcr0 := cr_pos (by omega : 1 ≤ k)
    have : c1 * ((k : ℝ) ^ (2 / 3 : ℝ) - 1) ≤ c1 * (((k : ℝ) - 1) * cr k) := by
      apply mul_le_mul_of_nonneg_left _ hc1.le
      nlinarith
    linarith
  have htend : Filter.Tendsto (fun k : ℕ => σ 1 + c1 * ((k : ℝ) ^ (2 / 3 : ℝ) - 1)) Filter.atTop
      Filter.atTop := by
    have h1 : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (2 / 3 : ℝ)) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_add_const_left _ _
      (Filter.Tendsto.const_mul_atTop hc1 (Filter.tendsto_atTop_add_const_right _ _ h1))
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop (s + |s - σ 1|))
  set M' := max M 2
  obtain ⟨ks, hks, hmin⟩ := Finset.exists_min_image (Finset.Icc 1 M') (fun k => |s - σ k|)
    ⟨1, by simp [M']⟩
  refine ⟨ks, (Finset.mem_Icc.mp hks).1, fun k hk => ?_⟩
  by_cases hkM : k ≤ M'
  · exact hmin k (Finset.mem_Icc.mpr ⟨hk, hkM⟩)
  · have hk2 : 2 ≤ k := by have := le_max_right M 2; omega
    have hkM2 : M ≤ k := by have := le_max_left M 2; omega
    have h1 := (hM k hkM2).trans (hlow k hk2)
    have h2 : σ k - s ≤ |s - σ k| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have h3 := hmin 1 (by simp [M'])
    linarith

/-! ### Pointwise bounds -/

lemma g_le_of_abs_ge {ε d m : ℝ} (_hε : 0 ≤ ε) (hm : 0 < m) (hd : m ≤ |d|) :
    nearT ε d * (|d| + 1) ≤ ε ^ 2 / m ^ 2 + ε ^ 2 / m := by
  have hd0 : d ≠ 0 := by intro h; rw [h] at hd; simp at hd; linarith
  have h1 := nearT_le_div (ε := ε) hd0
  have h2 := nearT_mul_abs_le_div (ε := ε) hd0
  have e1 : ε ^ 2 / d ^ 2 ≤ ε ^ 2 / m ^ 2 := by
    rw [← sq_abs d]; exact div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity) (by gcongr)
  have e2 : ε ^ 2 / |d| ≤ ε ^ 2 / m := div_le_div_of_nonneg_left (sq_nonneg ε) hm hd
  calc nearT ε d * (|d| + 1) = nearT ε d * |d| + nearT ε d := by ring
    _ ≤ ε ^ 2 / m + ε ^ 2 / m ^ 2 := add_le_add (h2.trans e2) (h1.trans e1)
    _ = _ := by ring

lemma case_A {c1 C0 ε d : ℝ} {i k : ℕ} (hc1 : 0 < c1) (hC0 : 0 < C0) (hi : 1 ≤ i) (hik : i ≤ k)
    (hε : 0 ≤ ε) (hεb : ε ≤ C0 * cr k) (hd : c1 / 2 * ((i : ℝ) * cr k) ≤ |d|) :
    nearT ε d * (|d| + 1) ≤ (4 * C0 ^ 2 / c1 ^ 2 + 2 * C0 ^ 2 / c1) * kern i := by
  have hk : 1 ≤ k := hi.trans hik
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hck := cr_pos hk
  have hci := cr_pos hi
  have hm : 0 < c1 / 2 * ((i : ℝ) * cr k) := by positivity
  refine (g_le_of_abs_ge hε hm hd).trans ?_
  have hε2 : ε ^ 2 ≤ (C0 * cr k) ^ 2 := by gcongr
  have hcc : cr k ≤ cr i := cr_anti hi hik
  have hinv := cr_ge_inv hi
  have t1 : ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr k)) ^ 2 ≤ 4 * C0 ^ 2 / c1 ^ 2 * kern i := by
    calc ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr k)) ^ 2
        ≤ (C0 * cr k) ^ 2 / (c1 / 2 * ((i : ℝ) * cr k)) ^ 2 := by gcongr
      _ = 4 * C0 ^ 2 / c1 ^ 2 * ((i : ℝ)⁻¹ * (i : ℝ)⁻¹) := by field_simp; norm_num
      _ ≤ 4 * C0 ^ 2 / c1 ^ 2 * kern i := by
          unfold kern
          gcongr
  have t2 : ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr k)) ≤ 2 * C0 ^ 2 / c1 * kern i := by
    calc ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr k))
        ≤ (C0 * cr k) ^ 2 / (c1 / 2 * ((i : ℝ) * cr k)) := by gcongr
      _ = 2 * C0 ^ 2 / c1 * ((i : ℝ)⁻¹ * cr k) := by field_simp
      _ ≤ 2 * C0 ^ 2 / c1 * kern i := by
          unfold kern
          gcongr
  nlinarith [t1, t2]

lemma case_B {c1 C0 ε d : ℝ} {i k ks : ℕ} (hc1 : 0 < c1) (hC0 : 0 < C0) (hi : 1 ≤ i) (hik : i ≤ ks)
    (_hk : 1 ≤ k) (hε : 0 ≤ ε) (hεb : ε ≤ C0 * cr k) (hρ : cr k ^ 2 ≤ 2 * cr ks ^ 2)
    (hd : c1 / 2 * ((i : ℝ) * cr ks) ≤ |d|) :
    nearT ε d * (|d| + 1) ≤ (8 * C0 ^ 2 / c1 ^ 2 + 4 * C0 ^ 2 / c1) * kern i := by
  have hks : 1 ≤ ks := hi.trans hik
  have hi0 : (0 : ℝ) < i := by exact_mod_cast hi
  have hcks := cr_pos hks
  have hci := cr_pos hi
  have hm : 0 < c1 / 2 * ((i : ℝ) * cr ks) := by positivity
  refine (g_le_of_abs_ge hε hm hd).trans ?_
  have hε2 : ε ^ 2 ≤ (C0 * cr k) ^ 2 := by gcongr
  have hcc : cr ks ≤ cr i := cr_anti hi hik
  have hinv := cr_ge_inv hi
  have hε3 : ε ^ 2 ≤ 2 * C0 ^ 2 * cr ks ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hρ (sq_nonneg C0)]
  have t1 : ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr ks)) ^ 2 ≤ 8 * C0 ^ 2 / c1 ^ 2 * kern i := by
    calc ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr ks)) ^ 2
        ≤ (2 * C0 ^ 2 * cr ks ^ 2) / (c1 / 2 * ((i : ℝ) * cr ks)) ^ 2 := by gcongr
      _ = 8 * C0 ^ 2 / c1 ^ 2 * ((i : ℝ)⁻¹ * (i : ℝ)⁻¹) := by field_simp; ring
      _ ≤ 8 * C0 ^ 2 / c1 ^ 2 * kern i := by
          unfold kern
          gcongr
  have t2 : ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr ks)) ≤ 4 * C0 ^ 2 / c1 * kern i := by
    calc ε ^ 2 / (c1 / 2 * ((i : ℝ) * cr ks))
        ≤ (2 * C0 ^ 2 * cr ks ^ 2) / (c1 / 2 * ((i : ℝ) * cr ks)) := by gcongr
      _ = 4 * C0 ^ 2 / c1 * ((i : ℝ)⁻¹ * cr ks) := by field_simp; ring
      _ ≤ 4 * C0 ^ 2 / c1 * kern i := by
          unfold kern
          gcongr
  nlinarith [t1, t2]

lemma case_C {c1 C0 ε d : ℝ} {k ks : ℕ} (hc1 : 0 < c1) (hC0 : 0 < C0) (hk : 1 ≤ k) (hks : 1 ≤ ks)
    (hε : 0 ≤ ε) (hεb : ε ≤ C0 * cr k)
    (hd : c1 / 4 * ((ks : ℝ) * cr ks) ≤ |d|) :
    nearT ε d * (|d| + 1) ≤ (16 * C0 ^ 2 / c1 ^ 2 + 4 * C0 ^ 2 / c1) * (cr k ^ 2 * cr ks ^ 2) := by
  have hks0 : (0 : ℝ) < ks := by exact_mod_cast hks
  have hcks := cr_pos hks
  have hck := cr_pos hk
  have hm : 0 < c1 / 4 * ((ks : ℝ) * cr ks) := by positivity
  refine (g_le_of_abs_ge hε hm hd).trans ?_
  have hε2 : ε ^ 2 ≤ (C0 * cr k) ^ 2 := by gcongr
  have hcube := cr_cube hks
  have hkcr : (ks : ℝ) * cr ks ^ 3 = 1 := by rw [hcube]; field_simp
  have hle1 := cr_le_one hks
  have e1 : 1 / ((ks : ℝ) * cr ks) = cr ks ^ 2 := by
    field_simp; nlinarith [hkcr]
  have t1 : ε ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks)) ^ 2 ≤ 16 * C0 ^ 2 / c1 ^ 2 * (cr k ^ 2 * cr ks ^ 2) := by
    calc ε ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks)) ^ 2
        ≤ (C0 * cr k) ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks)) ^ 2 := by gcongr
      _ = 16 * C0 ^ 2 / c1 ^ 2 * (cr k ^ 2 * (1 / ((ks : ℝ) * cr ks)) ^ 2) := by
          field_simp; norm_num
      _ = 16 * C0 ^ 2 / c1 ^ 2 * (cr k ^ 2 * cr ks ^ 4) := by rw [e1]; ring
      _ ≤ 16 * C0 ^ 2 / c1 ^ 2 * (cr k ^ 2 * cr ks ^ 2) := by
          have h4 : cr ks ^ 4 ≤ cr ks ^ 2 := by
            nlinarith [sq_nonneg (cr ks), pow_le_one₀ hcks.le hle1 (n := 2)]
          have h16 : 0 ≤ 16 * C0 ^ 2 / c1 ^ 2 * cr k ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h4 h16]
  have t2 : ε ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks)) ≤ 4 * C0 ^ 2 / c1 * (cr k ^ 2 * cr ks ^ 2) := by
    calc ε ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks))
        ≤ (C0 * cr k) ^ 2 / (c1 / 4 * ((ks : ℝ) * cr ks)) := by gcongr
      _ = 4 * C0 ^ 2 / c1 * (cr k ^ 2 * (1 / ((ks : ℝ) * cr ks))) := by field_simp
      _ = 4 * C0 ^ 2 / c1 * (cr k ^ 2 * cr ks ^ 2) := by rw [e1]
  nlinarith [t1, t2]

lemma kernZ_nonneg : 0 ≤ kernZ := tsum_nonneg kern_nonneg

/-- **The near-pair sum** (`rem:P1.2`, proof of (2), Step 3 (iii), the four ranges): uniformly in `s`, in the
sites with separation `c_1` and in the widths `ε_k ≤ C_0 k^{-1/3}`,
`∑_{2 ≤ k ≤ n} T_k (|s - σ_k| + 1) ≤ C`, `T_k = ε_k²/((s - σ_k)² + ε_k²)`. -/
theorem nearSum_le {c1 C0 : ℝ} (hc1 : 0 < c1) (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ ε : ℕ → ℝ),
      (∀ j k : ℕ, 1 ≤ j → j < k → c1 * (((k : ℝ) - j) * cr k) ≤ σ k - σ j) →
      (∀ k : ℕ, 2 ≤ k → 0 ≤ ε k ∧ ε k ≤ C0 * cr k) →
      ∀ (s : ℝ) (n : ℕ), ∑ k ∈ Icc 2 n, nearT (ε k) (s - σ k) * (|s - σ k| + 1) ≤ C := by
  set αA : ℝ := 4 * C0 ^ 2 / c1 ^ 2 + 2 * C0 ^ 2 / c1 with hαA
  set αB : ℝ := 8 * C0 ^ 2 / c1 ^ 2 + 4 * C0 ^ 2 / c1 with hαB
  set γ : ℝ := 16 * C0 ^ 2 / c1 ^ 2 + 4 * C0 ^ 2 / c1 with hγ
  have hαA0 : 0 ≤ αA := by positivity
  have hαB0 : 0 ≤ αB := by positivity
  have hγ0 : 0 ≤ γ := by positivity
  refine ⟨(1 + C0 / 2) + (αA + αB) * kernZ + 3 * γ + 1, by
    have := kernZ_nonneg; positivity, ?_⟩
  intro σ ε hsep hε s n
  obtain ⟨ks, hks1, hmin⟩ := exists_nearest hc1 σ hsep s
  have hcks := cr_pos hks1
  have hcks1 := cr_le_one hks1
  have hpt : ∀ k ∈ Icc 2 n, nearT (ε k) (s - σ k) * (|s - σ k| + 1) ≤
      (if k = ks then 1 + C0 / 2 else 0) + (if ks < k then αA * kern (k - ks) else 0) +
      (if k < ks ∧ ks ≤ 2 * k then αB * kern (ks - k) else 0) +
      (if 2 * k < ks then γ * (cr k ^ 2 * cr ks ^ 2) else 0) := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk1 : 1 ≤ k := by omega
    obtain ⟨hε0, hεb⟩ := hε k hk2
    have hck := cr_pos hk1
    have hck1 := cr_le_one hk1
    have hmk := hmin k hk1
    have hhalf : |σ k - σ ks| ≤ 2 * |s - σ k| := by
      have : |σ k - σ ks| ≤ |σ k - s| + |s - σ ks| := by
        have := abs_sub_le (σ k) s (σ ks); exact this
      rw [abs_sub_comm (σ k) s] at this
      linarith
    by_cases h1 : k = ks
    · subst h1
      have hT := nearT_le_one (ε k) (s - σ k)
      have hT2 := nearT_mul_abs_le_half (ε := ε k) (d := s - σ k) hε0
      have hcr : ε k ≤ C0 := hεb.trans (by nlinarith)
      have : nearT (ε k) (s - σ k) * (|s - σ k| + 1) ≤ 1 + C0 / 2 := by
        nlinarith [nearT_nonneg (ε k) (s - σ k)]
      simp only [ite_true, lt_irrefl, ite_false]
      have h4 : ¬ (2 * k < k) := by omega
      simp [h4, this]
    · have hne : ¬ (k = ks) := h1
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · -- k < ks
        have hs := hsep k ks hk1 hlt
        have hcast : (((ks - k : ℕ)) : ℝ) = (ks : ℝ) - k := by
          rw [Nat.cast_sub hlt.le]
        have hfull : c1 / 2 * (((ks - k : ℕ) : ℝ) * cr ks) ≤ |s - σ k| := by
          rw [hcast]
          have : σ ks - σ k ≤ |σ k - σ ks| := by rw [abs_sub_comm]; exact le_abs_self _
          nlinarith
        by_cases h2 : 2 * k < ks
        · -- case C
          have hks0 : (ks : ℝ) / 2 ≤ (ks : ℝ) - k := by
            have : (2 * k : ℝ) < ks := by exact_mod_cast h2
            linarith
          have hd : c1 / 4 * ((ks : ℝ) * cr ks) ≤ |s - σ k| := by
            rw [hcast] at hfull
            have : c1 / 2 * (((ks : ℝ) / 2) * cr ks) ≤ c1 / 2 * (((ks : ℝ) - k) * cr ks) := by gcongr
            nlinarith
          have := case_C hc1 hC0 hk1 hks1 hε0 hεb hd
          have h3 : ¬ (k = ks) := hne
          have h4 : ¬ (ks < k) := by omega
          have h5 : ¬ (k < ks ∧ ks ≤ 2 * k) := by omega
          simp only [h3, h4, h5, h2, ite_false, ite_true, zero_add]
          exact this
        · -- case B
          have h2' : ks ≤ 2 * k := by omega
          have hρ : cr k ^ 2 ≤ 2 * cr ks ^ 2 := by
            have hcc : cr ks ≤ cr k := cr_anti hk1 hlt.le
            have c3k := cr_cube hk1
            have c3s := cr_cube hks1
            have hkk : (1 : ℝ) / k ≤ 2 * (1 / ks) := by
              have : (ks : ℝ) ≤ 2 * k := by exact_mod_cast h2'
              have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
              have hks0 : (0 : ℝ) < ks := by exact_mod_cast hks1
              rw [div_le_iff₀ hk0]
              field_simp
              nlinarith
            have h6 : cr ks * cr k ^ 2 ≤ cr k ^ 3 := by nlinarith [sq_nonneg (cr k)]
            have h7 : cr k ^ 3 ≤ 2 * cr ks ^ 3 := by
              rw [c3k, c3s]; simpa [one_div] using hkk
            have h8 : cr ks * cr k ^ 2 ≤ cr ks * (2 * cr ks ^ 2) := by nlinarith
            exact le_of_mul_le_mul_left h8 hcks
          have hks_le : ks - k ≤ ks := Nat.sub_le _ _
          have := case_B (ks := ks) hc1 hC0 (by omega : 1 ≤ ks - k) hks_le hk1 hε0 hεb hρ hfull
          have h3 : ¬ (k = ks) := hne
          have h4 : ¬ (ks < k) := by omega
          have h5 : (k < ks ∧ ks ≤ 2 * k) := ⟨hlt, h2'⟩
          simp only [h3, h4, h5, h2, ite_false, ite_true, zero_add, add_zero, and_self]
          exact this
      · -- ks < k
        have hs := hsep ks k hks1 hgt
        have hcast : (((k - ks : ℕ)) : ℝ) = (k : ℝ) - ks := by
          rw [Nat.cast_sub hgt.le]
        have hfull : c1 / 2 * (((k - ks : ℕ) : ℝ) * cr k) ≤ |s - σ k| := by
          rw [hcast]
          have : σ k - σ ks ≤ |σ k - σ ks| := le_abs_self _
          nlinarith
        have := case_A hc1 hC0 (by omega : 1 ≤ k - ks) (by omega : k - ks ≤ k) hε0 hεb hfull
        have h3 : ¬ (k = ks) := hne
        have h5 : ¬ (k < ks ∧ ks ≤ 2 * k) := by omega
        have h6 : ¬ (2 * k < ks) := by omega
        simp only [h3, hgt, h5, h6, ite_false, ite_true, zero_add, add_zero]
        exact this
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have sA : ∑ k ∈ Icc 2 n, (if ks < k then αA * kern (k - ks) else 0) ≤ αA * kernZ := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    gcongr
    refine sum_kern_comp_le _ (fun k => k - ks) ?_
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    omega
  have sB : ∑ k ∈ Icc 2 n, (if k < ks ∧ ks ≤ 2 * k then αB * kern (ks - k) else 0) ≤ αB * kernZ := by
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    gcongr
    refine sum_kern_comp_le _ (fun k => ks - k) ?_
    intro a ha b hb hab
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    omega
  have sC : ∑ k ∈ Icc 2 n, (if 2 * k < ks then γ * (cr k ^ 2 * cr ks ^ 2) else 0) ≤ 3 * γ := by
    rw [← Finset.sum_filter]
    have hsub : (Icc 2 n).filter (fun k => 2 * k < ks) ⊆ Icc 1 ks := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    calc ∑ k ∈ (Icc 2 n).filter (fun k => 2 * k < ks), γ * (cr k ^ 2 * cr ks ^ 2)
        ≤ ∑ k ∈ Icc 1 ks, γ * (cr k ^ 2 * cr ks ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => ?_)
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
          have := cr_pos hk1
          positivity
      _ = γ * cr ks ^ 2 * ∑ k ∈ Icc 1 ks, cr k ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      _ ≤ γ * cr ks ^ 2 * (3 / cr ks) := by
          gcongr
          exact sum_cr_sq_le ks hks1
      _ = 3 * γ * cr ks := by field_simp
      _ ≤ 3 * γ := by nlinarith
  have sE : ∑ k ∈ Icc 2 n, (if k = ks then 1 + C0 / 2 else 0) ≤ 1 + C0 / 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  nlinarith [sA, sB, sC, sE]

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nearSum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nearSum_le

end FormalResearch.ModularBootstrap.Upper.Ramped
