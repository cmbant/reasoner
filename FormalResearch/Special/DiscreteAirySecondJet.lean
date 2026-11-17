module

public import FormalResearch.Special.DiscreteAirySecondODE
public import FormalResearch.Special.AiryParametrixTaylor

/-!
# Second-order Airy parametrix, part 3: a small calculus of third-order jets with uniform remainders

All expansions of the second-order construction are *uniform* in the parameters (`q`, the jets of the data, the sign and the
size of `t`).  This module packages the bookkeeping once.  Over a parameter type `α` with a domain `D : α → Prop` and a
"small parameter" `hh : α → ℝ` (`= h = t³`, `|hh| ≤ 1` on `D`):

* `SOB D hh n f` : `|f| ≤ K |hh|^n` on `D` for some `K ≥ 0` (`SOB 0` is boundedness);
* `Ex3 D hh f c0 c1 c2` : `f = c0 + hh c1 + hh² c2 + SOB 3` with bounded coefficients; closed under `+`, `*` (truncated
  convolution), multiplication by `hh`, and composition with smooth functions with bounded derivatives
  (`Ex3.of_taylor3`, `Ex3.of_taylor_h`, `Ex3.of_taylor_h2`, via the Taylor lemmas `sj_taylor1/2/3` built on `apx_taylor_chain`).

Everything is proved; constants existential.  This is the replacement of the explicit-constant bookkeeping of the first-order
proof (`sk_even_odd`, `apu_PA`).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

section Calc

variable {α : Type*}

/-- `f = O(|hh|^n)` uniformly on the domain `D`. -/
def SOB (D : α → Prop) (hh : α → ℝ) (n : ℕ) (f : α → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ a, D a → |f a| ≤ K * |hh a| ^ n

variable {D : α → Prop} {hh : α → ℝ}

lemma SOB.add {n : ℕ} {f g : α → ℝ} (hf : SOB D hh n f) (hg : SOB D hh n g) :
    SOB D hh n (fun a => f a + g a) := by
  obtain ⟨K1, hK1, h1⟩ := hf
  obtain ⟨K2, hK2, h2⟩ := hg
  refine ⟨K1 + K2, by positivity, fun a ha => ?_⟩
  calc |f a + g a| ≤ |f a| + |g a| := abs_add_le _ _
    _ ≤ K1 * |hh a| ^ n + K2 * |hh a| ^ n := add_le_add (h1 a ha) (h2 a ha)
    _ = _ := by ring

lemma SOB.neg {n : ℕ} {f : α → ℝ} (hf : SOB D hh n f) : SOB D hh n (fun a => -f a) := by
  obtain ⟨K, hK, h⟩ := hf
  exact ⟨K, hK, fun a ha => by rw [abs_neg]; exact h a ha⟩

lemma SOB.sub {n : ℕ} {f g : α → ℝ} (hf : SOB D hh n f) (hg : SOB D hh n g) :
    SOB D hh n (fun a => f a - g a) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

lemma SOB.const_mul {n : ℕ} {f : α → ℝ} (c : ℝ) (hf : SOB D hh n f) : SOB D hh n (fun a => c * f a) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨|c| * K, by positivity, fun a ha => ?_⟩
  rw [abs_mul]
  calc |c| * |f a| ≤ |c| * (K * |hh a| ^ n) := mul_le_mul_of_nonneg_left (h a ha) (abs_nonneg _)
    _ = _ := by ring

lemma SOB.mul {n m : ℕ} {f g : α → ℝ} (hf : SOB D hh n f) (hg : SOB D hh m g) :
    SOB D hh (n + m) (fun a => f a * g a) := by
  obtain ⟨K1, hK1, h1⟩ := hf
  obtain ⟨K2, hK2, h2⟩ := hg
  refine ⟨K1 * K2, by positivity, fun a ha => ?_⟩
  rw [abs_mul, pow_add]
  calc |f a| * |g a| ≤ (K1 * |hh a| ^ n) * (K2 * |hh a| ^ m) :=
        mul_le_mul (h1 a ha) (h2 a ha) (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma SOB.mono (hD : ∀ a, D a → |hh a| ≤ 1) {n m : ℕ} (hnm : m ≤ n) {f : α → ℝ} (hf : SOB D hh n f) :
    SOB D hh m f := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨K, hK, fun a ha => ?_⟩
  refine (h a ha).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg _) (hD a ha) hnm) hK

lemma SOB.congr {n : ℕ} {f g : α → ℝ} (hf : SOB D hh n f) (h : ∀ a, D a → f a = g a) : SOB D hh n g := by
  obtain ⟨K, hK, hb⟩ := hf
  exact ⟨K, hK, fun a ha => by rw [← h a ha]; exact hb a ha⟩

lemma SOB.dom {D' : α → Prop} {n : ℕ} {f : α → ℝ} (hf : SOB D hh n f) (h : ∀ a, D' a → D a) :
    SOB D' hh n f := by
  obtain ⟨K, hK, hb⟩ := hf
  exact ⟨K, hK, fun a ha => hb a (h a ha)⟩

lemma SOB.hh_pow (k : ℕ) : SOB D hh k (fun a => hh a ^ k) :=
  ⟨1, zero_le_one, fun a _ => by rw [abs_pow, one_mul]⟩

lemma SOB.zero (n : ℕ) : SOB D hh n (fun _ => 0) := ⟨0, le_rfl, fun a _ => by simp⟩

lemma SOB.bdd {f : α → ℝ} {M : ℝ} (h : ∀ a, D a → |f a| ≤ M) : SOB D hh 0 f :=
  ⟨|M|, abs_nonneg _, fun a ha => by simpa using (h a ha).trans (le_abs_self M)⟩

lemma SOB.const (c : ℝ) : SOB D hh 0 (fun _ => c) := SOB.bdd (M := |c|) fun _ _ => le_rfl

/-! ### Third-order expansions -/

/-- `f = c0 + hh c1 + hh² c2 + O(|hh|³)` with bounded coefficients. -/
def Ex3 (D : α → Prop) (hh : α → ℝ) (f c0 c1 c2 : α → ℝ) : Prop :=
  SOB D hh 3 (fun a => f a - (c0 a + hh a * c1 a + hh a ^ 2 * c2 a)) ∧
    SOB D hh 0 c0 ∧ SOB D hh 0 c1 ∧ SOB D hh 0 c2

lemma Ex3.add {f g c0 c1 c2 d0 d1 d2 : α → ℝ} (hf : Ex3 D hh f c0 c1 c2) (hg : Ex3 D hh g d0 d1 d2) :
    Ex3 D hh (fun a => f a + g a) (fun a => c0 a + d0 a) (fun a => c1 a + d1 a) (fun a => c2 a + d2 a) := by
  obtain ⟨r1, a0, a1, a2⟩ := hf
  obtain ⟨r2, b0, b1, b2⟩ := hg
  refine ⟨(r1.add r2).congr fun a _ => by ring, a0.add b0, a1.add b1, a2.add b2⟩

lemma Ex3.sub {f g c0 c1 c2 d0 d1 d2 : α → ℝ} (hf : Ex3 D hh f c0 c1 c2) (hg : Ex3 D hh g d0 d1 d2) :
    Ex3 D hh (fun a => f a - g a) (fun a => c0 a - d0 a) (fun a => c1 a - d1 a) (fun a => c2 a - d2 a) := by
  obtain ⟨r1, a0, a1, a2⟩ := hf
  obtain ⟨r2, b0, b1, b2⟩ := hg
  refine ⟨(r1.sub r2).congr fun a _ => by ring, a0.sub b0, a1.sub b1, a2.sub b2⟩

lemma Ex3.smul {f c0 c1 c2 : α → ℝ} (k : ℝ) (hf : Ex3 D hh f c0 c1 c2) :
    Ex3 D hh (fun a => k * f a) (fun a => k * c0 a) (fun a => k * c1 a) (fun a => k * c2 a) := by
  obtain ⟨r1, a0, a1, a2⟩ := hf
  refine ⟨(r1.const_mul k).congr fun a _ => by ring, a0.const_mul k, a1.const_mul k, a2.const_mul k⟩

lemma Ex3.congr {f f' c0 c1 c2 c0' c1' c2' : α → ℝ} (hf : Ex3 D hh f c0 c1 c2)
    (h : ∀ a, D a → f a = f' a) (h0 : ∀ a, D a → c0 a = c0' a) (h1 : ∀ a, D a → c1 a = c1' a)
    (h2 : ∀ a, D a → c2 a = c2' a) : Ex3 D hh f' c0' c1' c2' := by
  obtain ⟨r, a0, a1, a2⟩ := hf
  refine ⟨r.congr fun a ha => ?_, a0.congr h0, a1.congr h1, a2.congr h2⟩
  rw [h a ha, h0 a ha, h1 a ha, h2 a ha]

lemma Ex3.const {c : α → ℝ} (hc : SOB D hh 0 c) : Ex3 D hh c c (fun _ => 0) (fun _ => 0) :=
  ⟨(SOB.zero 3).congr fun a _ => by ring, hc, SOB.const 0, SOB.const 0⟩

lemma Ex3.of_sob {f : α → ℝ} (hf : SOB D hh 3 f) : Ex3 D hh f (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨hf.congr fun a _ => by ring, SOB.const 0, SOB.const 0, SOB.const 0⟩

lemma Ex3.hh_self :
    Ex3 D hh hh (fun _ => 0) (fun _ => 1) (fun _ => 0) :=
  ⟨(SOB.zero 3).congr fun a _ => by ring, SOB.const 0, SOB.const 1, SOB.const 0⟩

/-- Boundedness of the truncated polynomial. -/
lemma SOB.poly (hD : ∀ a, D a → |hh a| ≤ 1) {c0 c1 c2 : α → ℝ} (h0 : SOB D hh 0 c0) (h1 : SOB D hh 0 c1)
    (h2 : SOB D hh 0 c2) : SOB D hh 0 (fun a => c0 a + hh a * c1 a + hh a ^ 2 * c2 a) := by
  have e1 : SOB D hh 0 (fun a => hh a * c1 a) :=
    ((SOB.hh_pow (D := D) (hh := hh) 1).mul h1).mono hD (Nat.zero_le _) |>.congr fun a _ => by simp
  have e2 : SOB D hh 0 (fun a => hh a ^ 2 * c2 a) :=
    (((SOB.hh_pow (D := D) (hh := hh) 2).mul h2).mono hD (Nat.zero_le _))
  exact (h0.add e1).add e2

/-- **Product.**  Truncated convolution. -/
lemma Ex3.mul (hD : ∀ a, D a → |hh a| ≤ 1) {f g c0 c1 c2 d0 d1 d2 : α → ℝ}
    (hf : Ex3 D hh f c0 c1 c2) (hg : Ex3 D hh g d0 d1 d2) :
    Ex3 D hh (fun a => f a * g a) (fun a => c0 a * d0 a) (fun a => c0 a * d1 a + c1 a * d0 a)
      (fun a => c0 a * d2 a + c1 a * d1 a + c2 a * d0 a) := by
  obtain ⟨rf, a0, a1, a2⟩ := hf
  obtain ⟨rg, b0, b1, b2⟩ := hg
  have pc := SOB.poly hD a0 a1 a2
  have pd := SOB.poly hD b0 b1 b2
  have t1 : SOB D hh 3 (fun a => (c0 a + hh a * c1 a + hh a ^ 2 * c2 a) *
      (g a - (d0 a + hh a * d1 a + hh a ^ 2 * d2 a))) := (pc.mul rg).congr fun a _ => by simp
  have t2 : SOB D hh 3 (fun a => (f a - (c0 a + hh a * c1 a + hh a ^ 2 * c2 a)) *
      (d0 a + hh a * d1 a + hh a ^ 2 * d2 a)) := (rf.mul pd).congr fun a _ => by simp
  have t3 : SOB D hh 3 (fun a => (f a - (c0 a + hh a * c1 a + hh a ^ 2 * c2 a)) *
      (g a - (d0 a + hh a * d1 a + hh a ^ 2 * d2 a))) :=
    (rf.mul rg).mono hD (by norm_num)
  have t4 : SOB D hh 3 (fun a => hh a ^ 3 * (c1 a * d2 a + c2 a * d1 a)) :=
    ((SOB.hh_pow (D := D) (hh := hh) 3).mul ((a1.mul b2).add (a2.mul b1))).congr fun a _ => by simp
  have t5 : SOB D hh 3 (fun a => hh a ^ 4 * (c2 a * d2 a)) :=
    (((SOB.hh_pow (D := D) (hh := hh) 4).mul (a2.mul b2)).mono hD (by norm_num : 3 ≤ 4 + 0))
  refine ⟨((((t1.add t2).add t3).add t4).add t5).congr fun a _ => by ring, a0.mul b0, ?_, ?_⟩
  · exact ((a0.mul b1).add (a1.mul b0)).congr fun a _ => by simp
  · exact (((a0.mul b2).add (a1.mul b1)).add (a2.mul b0)).congr fun a _ => by simp

/-- **Multiplication by `hh`** (loses one order, the `h²`-coefficient is the old `h¹` one). -/
lemma Ex3.mulh (hD : ∀ a, D a → |hh a| ≤ 1) {f c0 c1 c2 : α → ℝ} (hf : Ex3 D hh f c0 c1 c2) :
    Ex3 D hh (fun a => hh a * f a) (fun _ => 0) c0 c1 := by
  obtain ⟨rf, a0, a1, a2⟩ := hf
  have t1 : SOB D hh 3 (fun a => hh a * (f a - (c0 a + hh a * c1 a + hh a ^ 2 * c2 a))) :=
    (((SOB.hh_pow (D := D) (hh := hh) 1).mul rf).mono hD (by norm_num : 3 ≤ 1 + 3)).congr fun a _ => by simp
  have t2 : SOB D hh 3 (fun a => hh a ^ 3 * c2 a) :=
    ((SOB.hh_pow (D := D) (hh := hh) 3).mul a2).congr fun a _ => by simp
  exact ⟨(t1.add t2).congr fun a _ => by ring, SOB.const 0, a0, a1⟩

/-- Bounded `∈ SOB 0` data: the `h`-linear combination used for the output. -/
lemma Ex3.out {f c0 c1 c2 : α → ℝ} (hf : Ex3 D hh f c0 c1 c2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a, D a → |f a - (c0 a + hh a * c1 a + hh a ^ 2 * c2 a)| ≤ K * |hh a| ^ 3 := hf.1


/-! ### Taylor primitives -/

lemma sj_seg {x0 δ S t : ℝ} (h0 : |x0| ≤ S) (h1 : |x0 + δ| ≤ S) (ht : t ∈ uIcc 0 δ) : |x0 + t| ≤ S := by
  rw [abs_le] at h0 h1 ⊢
  rcases le_total 0 δ with hδ | hδ
  · rw [uIcc_of_le hδ] at ht
    constructor <;> linarith [ht.1, ht.2]
  · rw [uIcc_of_ge hδ] at ht
    constructor <;> linarith [ht.1, ht.2]

lemma sj_taylor3 {F F1 F2 F3 : ℝ → ℝ} {M S x0 δ : ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hF2 : ∀ x, HasDerivAt F2 (F3 x) x) (hb : ∀ x, |x| ≤ S → |F3 x| ≤ M) (h0 : |x0| ≤ S) (h1 : |x0 + δ| ≤ S) :
    |F (x0 + δ) - (F x0 + F1 x0 * δ + F2 x0 * δ ^ 2 / 2)| ≤ M * |δ| ^ 3 := by
  let Fk : ℕ → ℝ → ℝ := fun k => match k with | 0 => F | 1 => F1 | 2 => F2 | _ => F3
  have h := apx_taylor_chain 3 Fk x0 δ M (fun k hk t _ => by
      interval_cases k
      · exact hF _
      · exact hF1 _
      · exact hF2 _) (fun t ht => hb _ (sj_seg h0 h1 ht)) δ right_mem_uIcc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fk, Nat.factorial] at h
  norm_num at h
  convert h using 2

lemma sj_taylor2 {F F1 F2 : ℝ → ℝ} {M S x0 δ : ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hF1 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hb : ∀ x, |x| ≤ S → |F2 x| ≤ M) (h0 : |x0| ≤ S) (h1 : |x0 + δ| ≤ S) :
    |F (x0 + δ) - (F x0 + F1 x0 * δ)| ≤ M * |δ| ^ 2 := by
  let Fk : ℕ → ℝ → ℝ := fun k => match k with | 0 => F | 1 => F1 | _ => F2
  have h := apx_taylor_chain 2 Fk x0 δ M (fun k hk t _ => by
      interval_cases k
      · exact hF _
      · exact hF1 _) (fun t ht => hb _ (sj_seg h0 h1 ht)) δ right_mem_uIcc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fk, Nat.factorial] at h
  norm_num at h
  rw [sq_abs]; exact h

lemma sj_taylor1 {F F1 : ℝ → ℝ} {M S x0 δ : ℝ}
    (hF : ∀ x, HasDerivAt F (F1 x) x) (hb : ∀ x, |x| ≤ S → |F1 x| ≤ M) (h0 : |x0| ≤ S)
    (h1 : |x0 + δ| ≤ S) : |F (x0 + δ) - F x0| ≤ M * |δ| := by
  let Fk : ℕ → ℝ → ℝ := fun k => match k with | 0 => F | _ => F1
  have h := apx_taylor_chain 1 Fk x0 δ M (fun k hk t _ => by
      interval_cases k
      exact hF _) (fun t ht => hb _ (sj_seg h0 h1 ht)) δ right_mem_uIcc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fk, Nat.factorial] at h
  norm_num at h
  exact h

/-! ### Composition -/

lemma Ex3.sob1 (hD : ∀ a, D a → |hh a| ≤ 1) {δ d1 d2 : α → ℝ}
    (hδ : Ex3 D hh δ (fun _ => 0) d1 d2) : SOB D hh 1 δ := by
  obtain ⟨r, -, a1, a2⟩ := hδ
  have t1 : SOB D hh 1 (fun a => hh a * d1 a) :=
    ((SOB.hh_pow (D := D) (hh := hh) 1).mul a1).congr fun a _ => by simp
  have t2 : SOB D hh 1 (fun a => hh a ^ 2 * d2 a) :=
    (((SOB.hh_pow (D := D) (hh := hh) 2).mul a2).mono hD (by norm_num : 1 ≤ 2 + 0)).congr fun a _ => by simp
  have t3 : SOB D hh 1 (fun a => δ a - (0 + hh a * d1 a + hh a ^ 2 * d2 a)) := r.mono hD (by norm_num)
  exact ((t1.add t2).add t3).congr fun a _ => by ring

/-- the `|δ|^k ≤ K^k |hh|^k` consequence. -/
lemma SOB.pow_of_sob1 {δ : α → ℝ} (h : SOB D hh 1 δ) (k : ℕ) : SOB D hh k (fun a => |δ a| ^ k) := by
  obtain ⟨K, hK, hb⟩ := h
  refine ⟨K ^ k, by positivity, fun a ha => ?_⟩
  have := pow_le_pow_left₀ (abs_nonneg _) (by simpa using hb a ha) k
  simpa [abs_abs, mul_pow, abs_pow] using this

lemma Ex3.of_taylor3 (hD : ∀ a, D a → |hh a| ≤ 1) {F F1 F2 F3 : α → ℝ → ℝ} {M0 M1 M2 M3 S : ℝ} {x0 δ d1 d2 : α → ℝ}
    (hM3 : 0 ≤ M3)
    (hF : ∀ a, D a → ∀ x, HasDerivAt (F a) (F1 a x) x) (hF1 : ∀ a, D a → ∀ x, HasDerivAt (F1 a) (F2 a x) x)
    (hF2 : ∀ a, D a → ∀ x, HasDerivAt (F2 a) (F3 a x) x)
    (hb : ∀ a, D a → ∀ x, |x| ≤ S → |F a x| ≤ M0 ∧ |F1 a x| ≤ M1 ∧ |F2 a x| ≤ M2 ∧ |F3 a x| ≤ M3)
    (hx0 : ∀ a, D a → |x0 a| ≤ S) (hx1 : ∀ a, D a → |x0 a + δ a| ≤ S)
    (hδ : Ex3 D hh δ (fun _ => 0) d1 d2) :
    Ex3 D hh (fun a => F a (x0 a + δ a)) (fun a => F a (x0 a)) (fun a => F1 a (x0 a) * d1 a)
      (fun a => F1 a (x0 a) * d2 a + F2 a (x0 a) * d1 a ^ 2 / 2) := by
  have hs1 := Ex3.sob1 hD hδ
  obtain ⟨K, hK, hKb⟩ := hs1.pow_of_sob1 3
  have hrem : SOB D hh 3 (fun a => F a (x0 a + δ a) -
      (F a (x0 a) + F1 a (x0 a) * δ a + F2 a (x0 a) * δ a ^ 2 / 2)) := by
    refine ⟨M3 * K, by positivity, fun a ha => ?_⟩
    have := sj_taylor3 (hF a ha) (hF1 a ha) (hF2 a ha) (fun x hx => (hb a ha x hx).2.2.2) (hx0 a ha) (hx1 a ha)
    refine this.trans ?_
    calc M3 * |δ a| ^ 3 ≤ M3 * (K * |hh a| ^ 3) := mul_le_mul_of_nonneg_left (by simpa using hKb a ha) hM3
      _ = _ := by ring
  have c0 : SOB D hh 0 (fun a => F a (x0 a)) := SOB.bdd (M := M0) fun a ha => (hb a ha _ (hx0 a ha)).1
  have c1 : SOB D hh 0 (fun a => F1 a (x0 a)) := SOB.bdd (M := M1) fun a ha => (hb a ha _ (hx0 a ha)).2.1
  have c2 : SOB D hh 0 (fun a => F2 a (x0 a)) := SOB.bdd (M := M2) fun a ha => (hb a ha _ (hx0 a ha)).2.2.1
  have e1 := Ex3.mul hD (Ex3.const c1) hδ
  have e2 := Ex3.mul hD hδ hδ
  have e3 := Ex3.mul hD (Ex3.const c2) e2
  have e4 := ((Ex3.const c0).add e1).add (e3.smul (1 / 2))
  have := e4.add (Ex3.of_sob hrem)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring)

/-- `hh · F(x0 + δ)` with `F, F', F''` bounded (second-order Taylor suffices). -/
lemma Ex3.of_taylor_h (hD : ∀ a, D a → |hh a| ≤ 1) {F F1 F2 : α → ℝ → ℝ} {M0 M1 M2 S : ℝ} {x0 δ d1 d2 : α → ℝ}
    (hM2 : 0 ≤ M2)
    (hF : ∀ a, D a → ∀ x, HasDerivAt (F a) (F1 a x) x) (hF1 : ∀ a, D a → ∀ x, HasDerivAt (F1 a) (F2 a x) x)
    (hb : ∀ a, D a → ∀ x, |x| ≤ S → |F a x| ≤ M0 ∧ |F1 a x| ≤ M1 ∧ |F2 a x| ≤ M2)
    (hx0 : ∀ a, D a → |x0 a| ≤ S) (hx1 : ∀ a, D a → |x0 a + δ a| ≤ S)
    (hδ : Ex3 D hh δ (fun _ => 0) d1 d2) :
    Ex3 D hh (fun a => hh a * F a (x0 a + δ a)) (fun _ => 0) (fun a => F a (x0 a))
      (fun a => F1 a (x0 a) * d1 a) := by
  have hs1 := Ex3.sob1 hD hδ
  obtain ⟨K, hK, hKb⟩ := hs1.pow_of_sob1 2
  have hrem : SOB D hh 2 (fun a => F a (x0 a + δ a) - (F a (x0 a) + F1 a (x0 a) * δ a)) := by
    refine ⟨M2 * K, by positivity, fun a ha => ?_⟩
    have := sj_taylor2 (hF a ha) (hF1 a ha) (fun x hx => (hb a ha x hx).2.2) (hx0 a ha) (hx1 a ha)
    refine this.trans ?_
    calc M2 * |δ a| ^ 2 ≤ M2 * (K * |hh a| ^ 2) := mul_le_mul_of_nonneg_left (by simpa using hKb a ha) hM2
      _ = _ := by ring
  have c0 : SOB D hh 0 (fun a => F a (x0 a)) := SOB.bdd (M := M0) fun a ha => (hb a ha _ (hx0 a ha)).1
  have c1 : SOB D hh 0 (fun a => F1 a (x0 a)) := SOB.bdd (M := M1) fun a ha => (hb a ha _ (hx0 a ha)).2.1
  have e1 := Ex3.mul hD (Ex3.const c1) hδ
  have e2 := (Ex3.const c0).add e1
  have e3 := Ex3.mulh hD e2
  have e4 : SOB D hh 3 (fun a => hh a * (F a (x0 a + δ a) - (F a (x0 a) + F1 a (x0 a) * δ a))) :=
    ((SOB.hh_pow (D := D) (hh := hh) 1).mul hrem).congr fun a _ => by simp
  have := e3.add (Ex3.of_sob e4)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring)

/-- `hh² · F(x0 + δ)` with `F, F'` bounded (first-order Taylor). -/
lemma Ex3.of_taylor_h2 (hD : ∀ a, D a → |hh a| ≤ 1) {F F1 : α → ℝ → ℝ} {M0 M1 S : ℝ} {x0 δ d1 d2 : α → ℝ}
    (hM1 : 0 ≤ M1)
    (hF : ∀ a, D a → ∀ x, HasDerivAt (F a) (F1 a x) x)
    (hb : ∀ a, D a → ∀ x, |x| ≤ S → |F a x| ≤ M0 ∧ |F1 a x| ≤ M1)
    (hx0 : ∀ a, D a → |x0 a| ≤ S) (hx1 : ∀ a, D a → |x0 a + δ a| ≤ S)
    (hδ : Ex3 D hh δ (fun _ => 0) d1 d2) :
    Ex3 D hh (fun a => hh a ^ 2 * F a (x0 a + δ a)) (fun _ => 0) (fun _ => 0) (fun a => F a (x0 a)) := by
  have hs1 := Ex3.sob1 hD hδ
  obtain ⟨K, hK, hKb⟩ := hs1.pow_of_sob1 1
  have hrem : SOB D hh 1 (fun a => F a (x0 a + δ a) - F a (x0 a)) := by
    refine ⟨M1 * K, by positivity, fun a ha => ?_⟩
    have := sj_taylor1 (hF a ha) (fun x hx => (hb a ha x hx).2) (hx0 a ha) (hx1 a ha)
    refine this.trans ?_
    calc M1 * |δ a| ≤ M1 * (K * |hh a|) := mul_le_mul_of_nonneg_left (by simpa using hKb a ha) hM1
      _ = _ := by ring
  have e5 : SOB D hh 0 (fun a => F a (x0 a)) := SOB.bdd (M := M0) fun a ha => (hb a ha _ (hx0 a ha)).1
  have e4 : SOB D hh 3 (fun a => hh a ^ 2 * (F a (x0 a + δ a) - F a (x0 a))) :=
    ((SOB.hh_pow (D := D) (hh := hh) 2).mul hrem).congr fun a _ => by simp
  have e6 : Ex3 D hh (fun a => hh a ^ 2 * F a (x0 a)) (fun _ => 0) (fun _ => 0) (fun a => F a (x0 a)) :=
    ⟨(SOB.zero 3).congr fun a _ => by ring, SOB.const 0, SOB.const 0, e5⟩
  have := e6.add (Ex3.of_sob e4)
  refine this.congr (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring) (fun a _ => by ring)

end Calc

/-- info: 'FormalResearch.Special.Ex3.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.Ex3.mul

/-- info: 'FormalResearch.Special.Ex3.of_taylor3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.Ex3.of_taylor3

end FormalResearch.Special
