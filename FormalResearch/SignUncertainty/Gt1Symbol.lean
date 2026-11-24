module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# `GT.1` symbol algebra and the Cauchy lemma at fixed order

`SymBd N x₀ β M b` says that `b` is a symbol of order `β` and size `M` through order `N` on `(x₀, ∞)`:
`b` is `C^{N+1}` on `[x₀, ∞)` and `x ^ (β + k) * ‖b^{(k)}(x)‖ ≤ M` for `k ≤ N`, `x > x₀`.

Formalised here:
* closure of `SymBd` under sums, constant multiples, lowering the order `β`, and products (Leibniz rule, constant `2 ^ N`);
* `symBd_inv_pow_add`: `1 / (x + a) ^ p` is a symbol of order `p` for `x₀ ≥ 2 |a|`;
* `symBd_of_sector`: a function holomorphic on the sector `{x₀/2 < re w, |im w| < re w / 2}` with
  `‖g w‖ ≤ M ‖w‖ ^ (-β)` there restricts to a symbol of order `β` on `(x₀, ∞)` (Cauchy estimates on discs of radius `x/4`).

Status: proved (every statement is unconditional given its stated hypotheses).  The constants are explicit.
Not formalised here: the use of these symbols in the `GT.1` transfer (other modules).
-/

@[expose] public section

open Complex Filter Set Metric
open scoped Real Topology

namespace FormalResearch.SignUncertainty

/-- `b` is a symbol of order `β` and size `M` through order `N` on `(x₀, ∞)`. -/
structure SymBd (N : ℕ) (x₀ β M : ℝ) (b : ℝ → ℂ) : Prop where
  cd : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) b (Set.Ici x₀)
  bd : ∀ k : ℕ, k ≤ N → ∀ x > x₀, x ^ (β + (k : ℝ)) * ‖iteratedDeriv k b x‖ ≤ M

theorem gt1s_contDiffAt {N : ℕ} {x₀ x : ℝ} {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) b (Ici x₀)) (hx : x₀ < x) :
    ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) b x :=
  hb.contDiffAt (Filter.mem_of_superset (Ioi_mem_nhds hx) Ioi_subset_Ici_self)

theorem gt1s_contDiffAt_le {N k : ℕ} {x₀ x : ℝ} {b : ℝ → ℂ}
    (hb : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) b (Ici x₀)) (hx : x₀ < x) (hk : k ≤ N) :
    ContDiffAt ℝ (k : WithTop ℕ∞) b x :=
  (gt1s_contDiffAt hb hx).of_le (by exact_mod_cast (Nat.le_succ_of_le hk))

theorem SymBd.add {N : ℕ} {x₀ β M M' : ℝ} {b c : ℝ → ℂ} (hx₀ : 0 < x₀) (hb : SymBd N x₀ β M b)
    (hc : SymBd N x₀ β M' c) : SymBd N x₀ β (M + M') (fun x => b x + c x) where
  cd := hb.cd.add hc.cd
  bd k hk x hx := by
    have hxpos : 0 < x ^ (β + (k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have e : iteratedDeriv k (fun y => b y + c y) x = iteratedDeriv k b x + iteratedDeriv k c x :=
      iteratedDeriv_add (gt1s_contDiffAt_le hb.cd hx hk) (gt1s_contDiffAt_le hc.cd hx hk)
    rw [e]
    calc x ^ (β + (k : ℝ)) * ‖iteratedDeriv k b x + iteratedDeriv k c x‖
        ≤ x ^ (β + (k : ℝ)) * (‖iteratedDeriv k b x‖ + ‖iteratedDeriv k c x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hxpos.le
      _ = x ^ (β + (k : ℝ)) * ‖iteratedDeriv k b x‖ + x ^ (β + (k : ℝ)) * ‖iteratedDeriv k c x‖ := by
          ring
      _ ≤ M + M' := add_le_add (hb.bd k hk x hx) (hc.bd k hk x hx)

theorem SymBd.const_mul {N : ℕ} {x₀ β M : ℝ} {b : ℝ → ℂ} (t : ℂ) (hb : SymBd N x₀ β M b) :
    SymBd N x₀ β (‖t‖ * M) (fun x => t * b x) where
  cd := contDiffOn_const.mul hb.cd
  bd k hk x hx := by
    have e : iteratedDeriv k (fun y => t * b y) x = t * iteratedDeriv k b x :=
      iteratedDeriv_const_mul t (gt1s_contDiffAt_le hb.cd hx hk)
    rw [e, norm_mul]
    calc x ^ (β + (k : ℝ)) * (‖t‖ * ‖iteratedDeriv k b x‖)
        = ‖t‖ * (x ^ (β + (k : ℝ)) * ‖iteratedDeriv k b x‖) := by ring
      _ ≤ ‖t‖ * M := mul_le_mul_of_nonneg_left (hb.bd k hk x hx) (norm_nonneg _)

theorem SymBd.mono_order {N : ℕ} {x₀ β β' M : ℝ} {b : ℝ → ℂ} (hx₀ : 1 ≤ x₀) (hβ : β' ≤ β)
    (hb : SymBd N x₀ β M b) : SymBd N x₀ β' M b where
  cd := hb.cd
  bd k hk x hx := by
    have h1 : x ^ (β' + (k : ℝ)) ≤ x ^ (β + (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc x ^ (β' + (k : ℝ)) * ‖iteratedDeriv k b x‖
        ≤ x ^ (β + (k : ℝ)) * ‖iteratedDeriv k b x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ M := hb.bd k hk x hx

theorem gt1s_norm_iteratedFDerivWithin_Ioi {x₀ x : ℝ} (hx : x₀ < x) (f : ℝ → ℂ) (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i f (Ioi x₀) x‖ = ‖iteratedDeriv i f x‖ := by
  rw [iteratedFDerivWithin_of_isOpen i isOpen_Ioi (show x ∈ Ioi x₀ from hx),
    norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ)]

/-- Leibniz rule for the `k`-th derivative of a product of two `C^{N+1}` functions on `(x₀, ∞)`. -/
theorem gt1s_leibniz {N k : ℕ} {x₀ x : ℝ} {b c : ℝ → ℂ}
    (hb : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) b (Ici x₀))
    (hc : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) c (Ici x₀)) (hx : x₀ < x) (hk : k ≤ N) :
    ‖iteratedDeriv k (fun y => b y * c y) x‖ ≤
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedDeriv i b x‖ * ‖iteratedDeriv (k - i) c x‖ := by
  have hO : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) b (Ioi x₀) :=
    (hb.mono Ioi_subset_Ici_self).of_le (by exact_mod_cast Nat.le_succ N)
  have hO' : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) c (Ioi x₀) :=
    (hc.mono Ioi_subset_Ici_self).of_le (by exact_mod_cast Nat.le_succ N)
  have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ((N : ℕ) : WithTop ℕ∞)) (n := k)
    hO hO' isOpen_Ioi.uniqueDiffOn (show x ∈ Ioi x₀ from hx) (by exact_mod_cast hk)
  rw [← gt1s_norm_iteratedFDerivWithin_Ioi hx (fun y => b y * c y) k]
  refine hmul.trans (le_of_eq ?_)
  simp only [gt1s_norm_iteratedFDerivWithin_Ioi hx]

theorem SymBd.mul {N : ℕ} {x₀ β γ M M' : ℝ} {b c : ℝ → ℂ} (hx₀ : 0 < x₀) (hb : SymBd N x₀ β M b)
    (hc : SymBd N x₀ γ M' c) : SymBd N x₀ (β + γ) (2 ^ N * M * M') (fun x => b x * c x) where
  cd := hb.cd.mul hc.cd
  bd k hk x hx := by
    have hxpos : 0 < x := by linarith
    have hM : 0 ≤ M :=
      (mul_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x₀ + 1) _) (norm_nonneg _)).trans
        (hb.bd 0 (Nat.zero_le _) (x₀ + 1) (by linarith))
    have hM' : 0 ≤ M' :=
      (mul_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x₀ + 1) _) (norm_nonneg _)).trans
        (hc.bd 0 (Nat.zero_le _) (x₀ + 1) (by linarith))
    have hMM : 0 ≤ M * M' := mul_nonneg hM hM'
    calc x ^ (β + γ + (k : ℝ)) * ‖iteratedDeriv k (fun y => b y * c y) x‖
        ≤ x ^ (β + γ + (k : ℝ)) * ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℝ) * ‖iteratedDeriv i b x‖ * ‖iteratedDeriv (k - i) c x‖ :=
          mul_le_mul_of_nonneg_left (gt1s_leibniz hb.cd hc.cd hx hk)
            (Real.rpow_nonneg hxpos.le _)
      _ = ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ((x ^ (β + (i : ℝ)) * ‖iteratedDeriv i b x‖) *
              (x ^ (γ + ((k - i : ℕ) : ℝ)) * ‖iteratedDeriv (k - i) c x‖)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have e : x ^ (β + γ + (k : ℝ)) = x ^ (β + (i : ℝ)) * x ^ (γ + ((k - i : ℕ) : ℝ)) := by
            rw [← Real.rpow_add hxpos, Nat.cast_sub hik]
            congr 1
            ring
          rw [e]
          ring
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (M * M') := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hA : x ^ (β + (i : ℝ)) * ‖iteratedDeriv i b x‖ ≤ M :=
            hb.bd i (hik.trans hk) x hx
          have hB : x ^ (γ + ((k - i : ℕ) : ℝ)) * ‖iteratedDeriv (k - i) c x‖ ≤ M' :=
            hc.bd (k - i) ((Nat.sub_le k i).trans hk) x hx
          have hB0 : 0 ≤ x ^ (γ + ((k - i : ℕ) : ℝ)) * ‖iteratedDeriv (k - i) c x‖ :=
            mul_nonneg (Real.rpow_nonneg hxpos.le _) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul hA hB hB0 hM) (Nat.cast_nonneg _)
      _ = (2 : ℝ) ^ k * (M * M') := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose k
      _ ≤ (2 : ℝ) ^ N * (M * M') :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hMM
      _ = 2 ^ N * M * M' := by ring

theorem gt1s_rpow_le_add {a b t : ℝ} (ha : 0 < a) (hat : a ≤ t) (htb : t ≤ b) (s : ℝ) :
    t ^ s ≤ a ^ s + b ^ s := by
  rcases le_total 0 s with hs | hs
  · have h1 : t ^ s ≤ b ^ s := Real.rpow_le_rpow (by linarith) htb hs
    have h2 : 0 ≤ a ^ s := Real.rpow_nonneg ha.le s
    linarith
  · have h1 : t ^ s ≤ a ^ s := Real.rpow_le_rpow_of_nonpos ha hat hs
    have h2 : 0 ≤ b ^ s := Real.rpow_nonneg (ha.trans_le (hat.trans htb)).le s
    linarith

/-- `1 / (x + a) ^ p` is a symbol of order `p` on `[x₀, ∞)` when `2 |a| ≤ x₀`. -/
theorem symBd_inv_pow_add (N : ℕ) {a : ℝ} (p : ℕ) {x₀ : ℝ} (hx₀ : 2 * |a| ≤ x₀) (hx₀' : 0 < x₀) :
    ∃ M : ℝ, 0 ≤ M ∧ SymBd N x₀ (p : ℝ) M (fun x : ℝ => ((1 / (x + a) ^ p : ℝ) : ℂ)) := by
  have hpos : ∀ t : ℝ, x₀ ≤ t → 0 < t + a := fun t ht => by
    linarith [neg_abs_le a]
  have hform : ∀ k : ℕ, ∀ y : ℝ, -a < y →
      iteratedDeriv k (fun t : ℝ => ((1 / (t + a) ^ p : ℝ) : ℂ)) y =
        (((∏ i ∈ Finset.range k, (-(p : ℝ) - i)) * (y + a) ^ (-(p : ℝ) - k) : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero =>
      intro y hy
      have hya : 0 < y + a := by linarith
      simp only [iteratedDeriv_zero, Finset.prod_range_zero, Nat.cast_zero, sub_zero, one_mul]
      rw [Real.rpow_neg hya.le, Real.rpow_natCast, one_div]
    | succ k ih =>
      intro y hy
      have hya : 0 < y + a := by linarith
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv k (fun t : ℝ => ((1 / (t + a) ^ p : ℝ) : ℂ)) =ᶠ[𝓝 y]
          fun t : ℝ => (((∏ i ∈ Finset.range k, (-(p : ℝ) - i)) * (t + a) ^ (-(p : ℝ) - k) : ℝ) : ℂ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun t ht => ih t ht)
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun t : ℝ => t + a) 1 y := (hasDerivAt_id y).add_const a
      have h2 := h1.rpow_const (p := -(p : ℝ) - k) (Or.inl hya.ne')
      have h3 := h2.const_mul (∏ i ∈ Finset.range k, (-(p : ℝ) - i))
      have hc : HasDerivAt
          (fun t : ℝ => (((∏ i ∈ Finset.range k, (-(p : ℝ) - i)) * (t + a) ^ (-(p : ℝ) - k) : ℝ) : ℂ))
          ((((∏ i ∈ Finset.range k, (-(p : ℝ) - i)) * ((-(p : ℝ) - k) * (y + a) ^ (-(p : ℝ) - k - 1)) : ℝ)) : ℂ) y := by
        apply HasDerivAt.ofReal_comp
        convert h3 using 1
        ring
      rw [hc.deriv]
      congr 1
      have he : -(p : ℝ) - ((k + 1 : ℕ) : ℝ) = -(p : ℝ) - k - 1 := by push_cast; ring
      rw [he, Finset.prod_range_succ]
      ring
  have hkey : ∀ x : ℝ, 0 < x → ∀ s : ℝ, x ^ s * (x / 2) ^ (-s) = (2 : ℝ) ^ s := by
    intro x hx s
    have hxs : x ^ s ≠ 0 := (Real.rpow_pos_of_pos hx s).ne'
    have h2s : (2 : ℝ) ^ s ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) s).ne'
    rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg hx.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  refine ⟨∑ j ∈ Finset.range (N + 1), |∏ i ∈ Finset.range j, (-(p : ℝ) - i)| * (2 : ℝ) ^ ((p : ℝ) + j),
    Finset.sum_nonneg fun j _ => by positivity, ?_⟩
  have hcd : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞)
      (fun x : ℝ => ((1 / (x + a) ^ p : ℝ) : ℂ)) (Ici x₀) := by
    intro t ht
    apply ContDiffAt.contDiffWithinAt
    have hne : (t + a) ^ p ≠ 0 := (pow_pos (hpos t ht) p).ne'
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp t
      (contDiffAt_const.div ((contDiffAt_id.add contDiffAt_const).pow p) hne)
  refine ⟨hcd, fun k hk x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hax : x / 2 ≤ x + a := by linarith [neg_abs_le a]
  have hxa0 : 0 < x / 2 := by linarith
  have hneg : -(p : ℝ) - k ≤ 0 := by
    have := (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  rw [hform k x (by linarith [neg_le_abs a, abs_nonneg a])]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (hpos x hx.le) (-(p : ℝ) - k))]
  have hle : (x + a) ^ (-(p : ℝ) - k) ≤ (x / 2) ^ (-(p : ℝ) - k) :=
    Real.rpow_le_rpow_of_nonpos hxa0 hax hneg
  have hsingle : |∏ i ∈ Finset.range k, (-(p : ℝ) - i)| * (2 : ℝ) ^ ((p : ℝ) + k) ≤
      ∑ j ∈ Finset.range (N + 1), |∏ i ∈ Finset.range j, (-(p : ℝ) - i)| * (2 : ℝ) ^ ((p : ℝ) + j) :=
    Finset.single_le_sum
      (f := fun j : ℕ => |∏ i ∈ Finset.range j, (-(p : ℝ) - i)| * (2 : ℝ) ^ ((p : ℝ) + j))
      (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have hk2 : x ^ ((p : ℝ) + k) * (x / 2) ^ (-(p : ℝ) - k) = (2 : ℝ) ^ ((p : ℝ) + k) := by
    rw [show -(p : ℝ) - k = -((p : ℝ) + k) by ring]
    exact hkey x hx0 ((p : ℝ) + k)
  have hxr : 0 ≤ x ^ ((p : ℝ) + k) := Real.rpow_nonneg hx0.le _
  calc x ^ ((p : ℝ) + k) * (|∏ i ∈ Finset.range k, (-(p : ℝ) - i)| * (x + a) ^ (-(p : ℝ) - k))
      ≤ x ^ ((p : ℝ) + k) * (|∏ i ∈ Finset.range k, (-(p : ℝ) - i)| * (x / 2) ^ (-(p : ℝ) - k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (abs_nonneg _)) hxr
    _ = |∏ i ∈ Finset.range k, (-(p : ℝ) - i)| * (x ^ ((p : ℝ) + k) * (x / 2) ^ (-(p : ℝ) - k)) := by
        ring
    _ = |∏ i ∈ Finset.range k, (-(p : ℝ) - i)| * (2 : ℝ) ^ ((p : ℝ) + k) := by rw [hk2]
    _ ≤ _ := hsingle

/-- Cauchy lemma at fixed order: a function holomorphic on the sector `{x₀/2 < re w, |im w| < re w/2}`
with `‖g w‖ ≤ M ‖w‖^(-β)` there restricts to a symbol of order `β` on `(x₀, ∞)`. -/
theorem symBd_of_sector (N : ℕ) (β : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {x₀ M : ℝ} {g : ℂ → ℂ}, 0 < x₀ → 0 ≤ M →
    DifferentiableOn ℂ g {w : ℂ | x₀ / 2 < w.re ∧ |w.im| < w.re / 2} →
    (∀ w : ℂ, x₀ / 2 < w.re → |w.im| < w.re / 2 → ‖g w‖ ≤ M * ‖w‖ ^ (-β)) →
    SymBd N x₀ β (C * M) (fun x : ℝ => g (x : ℂ)) := by
  refine ⟨(∑ k ∈ Finset.range (N + 1), (k.factorial : ℝ) * 4 ^ k) *
    ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)),
    mul_nonneg (Finset.sum_nonneg fun k _ => by positivity) (by positivity), ?_⟩
  intro x₀ M g hx₀ hM hg hbd
  set S : Set ℂ := {w : ℂ | x₀ / 2 < w.re ∧ |w.im| < w.re / 2} with hS_def
  have hSopen : IsOpen S := by
    rw [hS_def]
    exact (isOpen_lt (f := fun _ : ℂ => x₀ / 2) (g := fun w : ℂ => w.re) continuous_const
      Complex.continuous_re).inter
      (isOpen_lt (f := fun w : ℂ => |w.im|) (g := fun w : ℂ => w.re / 2) (by fun_prop) (by fun_prop))
  have hmemS : ∀ y : ℝ, x₀ ≤ y → (y : ℂ) ∈ S := by
    intro y hy
    rw [hS_def]
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    constructor <;> linarith
  have hball : ∀ y : ℝ, x₀ < y → closedBall (y : ℂ) (y / 4) ⊆ S := by
    intro y hy w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w - y)
    have him := Complex.abs_im_le_norm (w - y)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
    have hd := abs_le.mp hre
    rw [hS_def]
    simp only [Set.mem_ofPred_eq]
    constructor
    · linarith [hd.1]
    · linarith [hd.1]
  have hsph : ∀ y : ℝ, x₀ < y → ∀ z ∈ sphere (y : ℂ) (y / 4),
      ‖g z‖ ≤ M * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β) := by
    intro y hy z hz
    have hy0 : 0 < y := by linarith
    have hzS : x₀ / 2 < z.re ∧ |z.im| < z.re / 2 := hball y hy (sphere_subset_closedBall hz)
    have hzr : ‖z - y‖ = y / 4 := by
      rw [mem_sphere, dist_eq_norm] at hz
      exact hz
    have hyn : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_of_nonneg hy0.le]
    have h1 : ‖z‖ ≤ y / 4 + y := by
      have := norm_add_le (z - y) (y : ℂ)
      rw [sub_add_cancel, hzr, hyn] at this
      exact this
    have h2 : y - y / 4 ≤ ‖z‖ := by
      have := norm_sub_norm_le (y : ℂ) z
      rw [hyn, norm_sub_rev, hzr] at this
      linarith
    have hzpow : ‖z‖ ^ (-β) ≤ ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β) := by
      have := gt1s_rpow_le_add (a := 3 / 4 * y) (b := 5 / 4 * y) (t := ‖z‖)
        (mul_pos (by norm_num) hy0) (by linarith) (by linarith) (-β)
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 4) hy0.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4) hy0.le] at this
      rw [add_mul]
      exact this
    calc ‖g z‖ ≤ M * ‖z‖ ^ (-β) := hbd z hzS.1 hzS.2
      _ ≤ M * (((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β)) :=
          mul_le_mul_of_nonneg_left hzpow hM
      _ = M * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β) := by ring
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ (iteratedDeriv k g) S := by
    intro k
    induction k with
    | zero => simpa using hg
    | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hSopen
  have hreal : ∀ k : ℕ, ∀ y : ℝ, x₀ < y →
      iteratedDeriv k (fun t : ℝ => g (t : ℂ)) y = iteratedDeriv k g (y : ℂ) := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have hev : iteratedDeriv k (fun t : ℝ => g (t : ℂ)) =ᶠ[𝓝 y]
          fun t : ℝ => iteratedDeriv k g (t : ℂ) :=
        Filter.eventually_of_mem (Ioi_mem_nhds hy) (fun t ht => ih t ht)
      rw [iteratedDeriv_succ, iteratedDeriv_succ, hev.deriv_eq]
      have hd : HasDerivAt (iteratedDeriv k g) (deriv (iteratedDeriv k g) (y : ℂ)) (y : ℂ) :=
        ((hdiff k).differentiableAt (hSopen.mem_nhds (hmemS y hy.le))).hasDerivAt
      exact hd.comp_ofReal.deriv
  have hcauchy : ∀ k : ℕ, k ≤ N → ∀ y : ℝ, x₀ < y →
      y ^ (β + (k : ℝ)) * ‖iteratedDeriv k g (y : ℂ)‖ ≤
        (∑ j ∈ Finset.range (N + 1), (j.factorial : ℝ) * 4 ^ j) *
          ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * M := by
    intro k hk y hy
    have hy0 : 0 < y := by linarith
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k
      (by linarith : (0 : ℝ) < y / 4) (hg.diffContOnCl_ball (hball y hy)) (hsph y hy)
    have hyβ : 0 < y ^ β := Real.rpow_pos_of_pos hy0 β
    have hyk : y ^ k ≠ 0 := pow_ne_zero _ hy0.ne'
    have e1 : y ^ (β + (k : ℝ)) = y ^ β * y ^ k := by
      rw [Real.rpow_add hy0, Real.rpow_natCast]
    have e2 : y ^ (-β) = (y ^ β)⁻¹ := Real.rpow_neg hy0.le β
    have hid : y ^ (β + (k : ℝ)) *
        ((k.factorial : ℝ) * (M * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β)) / (y / 4) ^ k)
        = (k.factorial : ℝ) * 4 ^ k * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * M := by
      rw [e1, e2, div_pow]
      field_simp
    have hsum : (k.factorial : ℝ) * 4 ^ k ≤ ∑ j ∈ Finset.range (N + 1), (j.factorial : ℝ) * 4 ^ j :=
      Finset.single_le_sum (f := fun j : ℕ => (j.factorial : ℝ) * 4 ^ j)
        (fun j _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    have hc0 : 0 ≤ (3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β) := by positivity
    calc y ^ (β + (k : ℝ)) * ‖iteratedDeriv k g (y : ℂ)‖
        ≤ y ^ (β + (k : ℝ)) * ((k.factorial : ℝ) * (M * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * y ^ (-β)) / (y / 4) ^ k) :=
          mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg hy0.le _)
      _ = (k.factorial : ℝ) * 4 ^ k * ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * M := hid
      _ ≤ (∑ j ∈ Finset.range (N + 1), (j.factorial : ℝ) * 4 ^ j) *
          ((3 / 4 : ℝ) ^ (-β) + (5 / 4 : ℝ) ^ (-β)) * M :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hc0) hM
  refine ⟨?_, ?_⟩
  · have hgC : ContDiffOn ℂ ((N + 1 : ℕ) : WithTop ℕ∞) g S := hg.contDiffOn hSopen
    have hgR : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) g S := hgC.restrict_scalars (𝕜 := ℝ)
    have hof : ContDiffOn ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) (Ici x₀) :=
      (show ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) (Complex.ofRealCLM : ℝ → ℂ) from Complex.ofRealCLM.contDiff).contDiffOn.mono (subset_univ _)
    exact hgR.comp hof (fun t ht => hmemS t ht)
  · intro k hk x hx
    rw [hreal k x hx]
    exact hcauchy k hk x hx

/-! ## Pinned dependency guards -/

/-- info: 'FormalResearch.SignUncertainty.gt1s_contDiffAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1s_contDiffAt

/-- info: 'FormalResearch.SignUncertainty.gt1s_contDiffAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1s_contDiffAt_le

/-- info: 'FormalResearch.SignUncertainty.SymBd.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymBd.add

/-- info: 'FormalResearch.SignUncertainty.SymBd.const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymBd.const_mul

/-- info: 'FormalResearch.SignUncertainty.SymBd.mono_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymBd.mono_order

/-- info: 'FormalResearch.SignUncertainty.gt1s_norm_iteratedFDerivWithin_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1s_norm_iteratedFDerivWithin_Ioi

/-- info: 'FormalResearch.SignUncertainty.gt1s_leibniz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1s_leibniz

/-- info: 'FormalResearch.SignUncertainty.SymBd.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SymBd.mul

/-- info: 'FormalResearch.SignUncertainty.gt1s_rpow_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1s_rpow_le_add

/-- info: 'FormalResearch.SignUncertainty.symBd_inv_pow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symBd_inv_pow_add

/-- info: 'FormalResearch.SignUncertainty.symBd_of_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms symBd_of_sector

end FormalResearch.SignUncertainty
