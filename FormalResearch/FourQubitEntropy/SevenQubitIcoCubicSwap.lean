import FormalResearch.FourQubitEntropy.SevenQubitIcoCubicForm

/-!
# From the mask sum to a weighted pair sum, and the integer tables of the icosahedral tensor

Generic, state-independent part of the cut-free evaluation of `V_r(ψ)` and its relatives
(see `SevenQubitIcoCubicForm`):

* `cubNatT_eq_cubR` (and `cubNat_eq_cubR`): the numerical trilinear mask sum equals
  `∑_{v,u<128} cfCount(z⊕v, z⊕u) · ψ(u) ψ(v) ψ(z⊕u⊕v)`, where `cfCount D E` is the number of masks `M`
  of the class with `D ⊆ M` and `E ∩ M = ∅` (double counting);
* the support-list evaluation (`cubI_eq_cubW`), for kernel checks that only visit the support of the
  tensor, and the integer tables `cfA`, `cfB` of `alphaCoefficient`, `betaCoefficient` as functions
  of `n < 128` (packed into big literals so that kernel evaluation is cheap);
* `cubicMaskSum_ico` (all three slots `ψ = α U + β V`) and `cubicMaskSumT_tab` (one trilinear form of
  `U = alphaReal`, `V = betaReal`): the cubic mask sums as combinations of the eight kernel-evaluated forms
  `cfK`, used by the class files `SevenQubitIcoCubicC2/C30/C31` and by `SevenQubitIcoContraction`.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### Double counting -/

/-- Number of numbers `M < 128` of the class `pN` with `D ⊆ M` and `E ∩ M = ∅` (bitwise). -/
def cfCount (pN : ℕ → Prop) [DecidablePred pN] (D E : ℕ) : ℕ :=
  ((Finset.range 128).filter fun M => pN M ∧ D &&& M = D ∧ E &&& M = 0).card

theorem xor_lt_128 {a b : ℕ} (ha : a < 128) (hb : b < 128) : a ^^^ b < 128 :=
  Nat.xor_lt_two_pow (n := 7) ha hb

theorem xor_cancel_self (z D : ℕ) : z ^^^ (z ^^^ D) = D := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem sum_xor_range {M : Type*} [AddCommMonoid M] (z : ℕ) (hz : z < 128) (F : ℕ → M) :
    ∑ D ∈ range 128, F D = ∑ v ∈ range 128, F (z ^^^ v) := by
  refine Finset.sum_nbij' (fun D => z ^^^ D) (fun v => z ^^^ v) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    exact Finset.mem_range.2 (xor_lt_128 hz (Finset.mem_range.1 hD))
  · intro D hD
    exact Finset.mem_range.2 (xor_lt_128 hz (Finset.mem_range.1 hD))
  · intro D _; exact xor_cancel_self z D
  · intro D _; exact xor_cancel_self z D
  · intro D _; simp only [xor_cancel_self]

theorem xor3_aux (z u v : ℕ) : z ^^^ ((z ^^^ v) ^^^ (z ^^^ u)) = z ^^^ u ^^^ v := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases z.testBit i <;> cases u.testBit i <;> cases v.testBit i <;> rfl

/-- Cubic weighted pair sum over `ℝ`. -/
def cubR (w : ℕ → ℕ → ℕ) (f g h : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ v ∈ range 128, ∑ u ∈ range 128, (w (z ^^^ v) (z ^^^ u) : ℝ) * (f u * g v * h (z ^^^ u ^^^ v))

theorem cubNatT_eq_cubR (pN : ℕ → Prop) [DecidablePred pN] (f g h : ℕ → ℝ) (z : ℕ)
    (hz : z < 128) : cubNatT pN f g h z = cubR (cfCount pN) f g h z := by
  have e : ∀ (c : Prop) [Decidable c] (s : Finset ℕ) (f : ℕ → ℝ),
      (if c then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if c then f i else 0 := by
    intro c _ s f; split_ifs <;> simp
  have h1 : cubNatT pN f g h z = ∑ M ∈ range 128, ∑ D ∈ range 128, ∑ E ∈ range 128,
      if pN M ∧ D &&& M = D ∧ E &&& M = 0 then f (z ^^^ E) * g (z ^^^ D) * h (z ^^^ (D ^^^ E))
        else 0 := by
    unfold cubNatT
    refine Finset.sum_congr rfl fun M _ => ?_
    by_cases h : pN M
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun D _ => ?_
      by_cases h' : D &&& M = D
      · rw [if_pos h']
        refine Finset.sum_congr rfl fun E _ => ?_
        by_cases h'' : E &&& M = 0
        · simp [h, h', h'']
        · simp [h'']
      · simp [h']
    · simp [h]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ D ∈ range 128, ∑ M ∈ range 128, ∑ E ∈ range 128,
      (if pN M ∧ D &&& M = D ∧ E &&& M = 0 then
        f (z ^^^ E) * g (z ^^^ D) * h (z ^^^ (D ^^^ E)) else 0) =
      ∑ E ∈ range 128, (cfCount pN D E : ℝ) * (f (z ^^^ E) * g (z ^^^ D) * h (z ^^^ (D ^^^ E))) := by
    intro D _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun E _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [Finset.sum_congr rfl h2]
  unfold cubR
  rw [sum_xor_range z hz]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [sum_xor_range z hz]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [xor_cancel_self, xor_cancel_self, xor3_aux]

theorem cubNat_eq_cubR (pN : ℕ → Prop) [DecidablePred pN] (ψ : ℕ → ℝ) (z : ℕ) (hz : z < 128) :
    cubNat pN ψ z = cubR (cfCount pN) ψ ψ ψ z := cubNatT_eq_cubR pN ψ ψ ψ z hz

/-- The expansion of `cubR` for `ψ = α f₁ + β f₂`. -/
theorem cubR_expand (w : ℕ → ℕ → ℕ) (a b : ℕ → ℝ) (α β : ℝ) (z : ℕ) :
    cubR w (fun n => α * a n + β * b n) (fun n => α * a n + β * b n) (fun n => α * a n + β * b n) z =
      α ^ 3 * cubR w a a a z +
      α ^ 2 * β * (cubR w a a b z + cubR w a b a z + cubR w b a a z) +
      α * β ^ 2 * (cubR w a b b z + cubR w b a b z + cubR w b b a z) + β ^ 3 * cubR w b b b z := by
  unfold cubR
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  ring

/-! ### Integer version and support lists -/

/-- Integer-valued cubic weighted pair sum. -/
def cubI (w : ℕ → ℕ → ℕ) (f g h : ℕ → ℤ) (z : ℕ) : ℤ :=
  ∑ v ∈ range 128, ∑ u ∈ range 128, (w (z ^^^ v) (z ^^^ u) : ℤ) * (f u * g v * h (z ^^^ u ^^^ v))

theorem cubR_cast (w : ℕ → ℕ → ℕ) (f g h : ℕ → ℤ) (z : ℕ) :
    cubR w (fun n => (f n : ℝ)) (fun n => (g n : ℝ)) (fun n => (h n : ℝ)) z =
      ((cubI w f g h z : ℤ) : ℝ) := by
  unfold cubR cubI
  push_cast
  rfl

/-- One term of the support-list sum: skip the evaluation when the weight is zero. -/
def cfTerm (w : ℕ) (x : ℤ) : ℤ := if w = 0 then 0 else (w : ℤ) * x

theorem cfTerm_eq (w : ℕ) (x : ℤ) : cfTerm w x = (w : ℤ) * x := by
  unfold cfTerm; split_ifs with h <;> simp [h]

/-- Support-list version of `cubI`. -/
def cubW (w : ℕ → ℕ → ℕ) (Lf Lg : List ℕ) (f g h : ℕ → ℤ) (z : ℕ) : ℤ :=
  (Lg.map fun v => (Lf.map fun u =>
    cfTerm (w (z ^^^ v) (z ^^^ u)) (f u * g v * h (z ^^^ u ^^^ v))).sum).sum

theorem sum_range_eq_list {M : Type*} [AddCommMonoid M] (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, x < 128) (F : ℕ → M) (hF : ∀ x < 128, F x ≠ 0 → x ∈ L) :
    ∑ x ∈ range 128, F x = (L.map F).sum := by
  rw [← List.sum_toFinset F hnd]
  symm
  apply Finset.sum_subset
  · intro x hx
    exact Finset.mem_range.2 (hL x (List.mem_toFinset.1 hx))
  · intro x hx hx'
    by_contra hne
    exact hx' (List.mem_toFinset.2 (hF x (Finset.mem_range.1 hx) hne))

theorem cubI_eq_cubW (w : ℕ → ℕ → ℕ) (Lf Lg : List ℕ) (f g h : ℕ → ℤ) (z : ℕ)
    (hf1 : Lf.Nodup) (hf2 : ∀ x ∈ Lf, x < 128) (hf3 : ∀ x < 128, f x ≠ 0 → x ∈ Lf)
    (hg1 : Lg.Nodup) (hg2 : ∀ x ∈ Lg, x < 128) (hg3 : ∀ x < 128, g x ≠ 0 → x ∈ Lg) :
    cubI w f g h z = cubW w Lf Lg f g h z := by
  unfold cubI cubW
  rw [sum_range_eq_list Lg hg1 hg2 _ ?_]
  · congr 1
    refine List.map_congr_left fun v hv => ?_
    rw [← sum_range_eq_list Lf hf1 hf2 _ ?_]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [cfTerm_eq]
    · intro u hu hne
      apply hf3 u hu
      intro h0
      apply hne
      simp [h0, cfTerm]
  · intro v hv hne
    apply hg3 v hv
    intro h0
    apply hne
    refine Finset.sum_eq_zero fun u _ => ?_
    simp [h0]

/-! ### The integer tables of the icosahedral tensor -/

/-- Bit `n` is set iff `alphaCoefficient (maskOfNat n) = 1`. -/
def cfAPos : ℕ := 172400637587266659092194983679040
/-- Bit `n` is set iff `alphaCoefficient (maskOfNat n) = -1`. -/
def cfANeg : ℕ := 2866796994626709371920266765496483840

/-- `alphaCoefficient (maskOfNat n)`, by bit lookup. -/
def cfA (n : ℕ) : ℤ := ((cfAPos >>> n) % 2 : ℕ) - ((cfANeg >>> n) % 2 : ℕ)
/-- `betaCoefficient (maskOfNat n)`: the two points `0111111` and `1000000`. -/
def cfB (n : ℕ) : ℤ := if n = 126 ∨ n = 1 then 1 else 0

theorem alphaCoefficient_maskOfNat : ∀ n < 128, alphaCoefficient (maskOfNat n) = cfA n := by
  decide +kernel

theorem betaCoefficient_maskOfNat : ∀ n < 128, betaCoefficient (maskOfNat n) = cfB n := by
  decide +kernel

/-- The support of `cfA` (30 points). -/
def cfSuppA : List ℕ :=
  [6, 10, 12, 18, 20, 24, 31, 34, 36, 40, 47, 48, 55, 59, 61, 66, 68, 72, 79, 80, 87, 91, 93, 96, 103,
    107, 109, 115, 117, 121]

/-- The support of `cfB` (2 points). -/
def cfSuppB : List ℕ := [1, 126]

theorem cfSuppA_spec :
    cfSuppA.Nodup ∧ (∀ x ∈ cfSuppA, x < 128) ∧ ∀ x < 128, cfA x ≠ 0 → x ∈ cfSuppA := by
  decide +kernel

theorem cfSuppB_spec :
    cfSuppB.Nodup ∧ (∀ x ∈ cfSuppB, x < 128) ∧ ∀ x < 128, cfB x ≠ 0 → x ∈ cfSuppB := by
  decide +kernel

/-! ### Tables of the weights `cfCount` and the assembly lemma -/

/-- Packed table of the weights: the field `4 (8a + b) + 2 d₀ + e₀` (8 bits) holds the number of masks of
the class containing `D` and avoiding `E`, where `a = |D|`, `b = |E|`, `d₀`, `e₀` are the bits `0` of
`D`, `E`; zero unless `D ∩ E = ∅`. -/
def cfWt (WP D E : ℕ) : ℕ :=
  if D &&& E = 0 then
    (WP >>> (8 * (4 * (8 * cfPc D + cfPc E) + 2 * (D &&& 1) + (E &&& 1)))) % 256
  else 0

theorem cfCount_nondisj (pN : ℕ → Prop) [DecidablePred pN] {D E : ℕ} (h : D &&& E ≠ 0) :
    cfCount pN D E = 0 := by
  unfold cfCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro M _ ⟨_, h1, h2⟩
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have a1 := congrArg (fun x => x.testBit i) h1
  have a2 := congrArg (fun x => x.testBit i) h2
  simp only [Nat.testBit_and, Nat.zero_testBit] at a1 a2 ⊢
  cases hD : D.testBit i <;> cases hE : E.testBit i <;> cases hM : M.testBit i <;>
    simp_all

theorem cfCount_eq_list (pN : ℕ → Prop) [DecidablePred pN] (L : List ℕ) (hnd : L.Nodup)
    (hL : ∀ x ∈ L, x < 128) (hcov : ∀ M < 128, pN M → M ∈ L) (D E : ℕ) :
    cfCount pN D E =
      (L.map fun M => if pN M ∧ D &&& M = D ∧ E &&& M = 0 then 1 else 0).sum := by
  unfold cfCount
  rw [Finset.card_filter]
  apply sum_range_eq_list L hnd hL
  intro x hx hne
  apply hcov x hx
  by_contra hp
  apply hne
  simp [hp]

theorem cubI_congr_weight (w w' : ℕ → ℕ → ℕ) (hw : ∀ D < 128, ∀ E < 128, w D E = w' D E)
    (f g h : ℕ → ℤ) (z : ℕ) (hz : z < 128) : cubI w f g h z = cubI w' f g h z := by
  unfold cubI
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun u hu => ?_
  rw [hw _ (xor_lt_128 hz (Finset.mem_range.1 hv)) _ (xor_lt_128 hz (Finset.mem_range.1 hu))]

theorem cubR_congr (w : ℕ → ℕ → ℕ) (f f' g g' h h' : ℕ → ℝ) (z : ℕ) (hz : z < 128)
    (hf : ∀ n < 128, f n = f' n) (hg : ∀ n < 128, g n = g' n) (hh : ∀ n < 128, h n = h' n) :
    cubR w f g h z = cubR w f' g' h' z := by
  unfold cubR
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun u hu => ?_
  have hv' := Finset.mem_range.1 hv
  have hu' := Finset.mem_range.1 hu
  rw [hf u hu', hg v hv', hh _ (xor_lt_128 (xor_lt_128 hz hu') hv')]

/-- The table selected by a boolean: `false ↦ cfA`, `true ↦ cfB`. -/
def cfTab : Bool → ℕ → ℤ
  | false => cfA
  | true => cfB

/-- Its support. -/
def cfSupp : Bool → List ℕ
  | false => cfSuppA
  | true => cfSuppB

theorem cfTab_supp (x : Bool) :
    (cfSupp x).Nodup ∧ (∀ s ∈ cfSupp x, s < 128) ∧ ∀ n < 128, cfTab x n ≠ 0 → n ∈ cfSupp x := by
  cases x
  · exact cfSuppA_spec
  · exact cfSuppB_spec

/-- Evaluation of one trilinear form `cubR (cfCount pN)` on the tables by the support-list sum with the
weight table `WP`. -/
theorem cubR_tab (pN : ℕ → Prop) [DecidablePred pN] (WP : ℕ)
    (hW : ∀ D < 128, ∀ E < 128, cfCount pN D E = cfWt WP D E) (z : ℕ) (hz : z < 128)
    (x y w : Bool) :
    cubR (cfCount pN) (fun n => (cfTab x n : ℝ)) (fun n => (cfTab y n : ℝ))
        (fun n => (cfTab w n : ℝ)) z =
      ((cubW (cfWt WP) (cfSupp x) (cfSupp y) (cfTab x) (cfTab y) (cfTab w) z : ℤ) : ℝ) := by
  rw [cubR_cast, cubI_congr_weight _ _ hW _ _ _ z hz]
  obtain ⟨a1, a2, a3⟩ := cfTab_supp x
  obtain ⟨b1, b2, b3⟩ := cfTab_supp y
  rw [cubI_eq_cubW _ _ _ _ _ _ z a1 a2 a3 b1 b2 b3]

theorem icosahedralState_maskOfNat (α β : ℝ) (n : ℕ) (hn : n < 128) :
    icosahedralState α β (maskOfNat n) = α * (cfA n : ℝ) + β * (cfB n : ℝ) := by
  unfold icosahedralState
  rw [alphaCoefficient_maskOfNat n hn, betaCoefficient_maskOfNat n hn]

/-- One trilinear form of the tables, evaluated by the support-list sum with the weight table `WP`. -/
def cfK (WP z : ℕ) (x y w : Bool) : ℝ :=
  ((cubW (cfWt WP) (cfSupp x) (cfSupp y) (cfTab x) (cfTab y) (cfTab w) z : ℤ) : ℝ)

/-- The cubic mask sum of the icosahedral state over a class of masks, as the combination of the eight
trilinear forms in the two integer tables, each evaluated by the support-list sum. -/
theorem cubicMaskSum_ico (P : (Fin 7 → Bool) → Prop) [DecidablePred P]
    (pN : ℕ → Prop) [DecidablePred pN] (hP : ∀ M < 128, P (maskOfNat M) ↔ pN M) (WP : ℕ)
    (hW : ∀ D < 128, ∀ E < 128, cfCount pN D E = cfWt WP D E)
    (α β : ℝ) (z : ℕ) (hz : z < 128) :
    cubicMaskSum (icosahedralState α β) (maskOfNat z) P =
      α ^ 3 * cfK WP z false false false +
      α ^ 2 * β * (cfK WP z false false true + cfK WP z false true false + cfK WP z true false false) +
      α * β ^ 2 * (cfK WP z false true true + cfK WP z true false true + cfK WP z true true false) +
      β ^ 3 * cfK WP z true true true := by
  rw [cubicMaskSum_nat P pN hP _ z hz, cubNat_eq_cubR _ _ z hz]
  have hψ : ∀ n < 128, icosahedralState α β (maskOfNat n) = α * (cfA n : ℝ) + β * (cfB n : ℝ) :=
    fun n hn => icosahedralState_maskOfNat α β n hn
  rw [cubR_congr _ _ (fun n => α * (cfA n : ℝ) + β * (cfB n : ℝ))
    _ (fun n => α * (cfA n : ℝ) + β * (cfB n : ℝ))
    _ (fun n => α * (cfA n : ℝ) + β * (cfB n : ℝ)) z hz hψ hψ hψ, cubR_expand]
  have e : ∀ x y w, cubR (cfCount pN) (fun n => (cfTab x n : ℝ)) (fun n => (cfTab y n : ℝ))
      (fun n => (cfTab w n : ℝ)) z = cfK WP z x y w := fun x y w => cubR_tab pN WP hW z hz x y w
  have e1 := e false false false
  have e2 := e false false true
  have e3 := e false true false
  have e4 := e true false false
  have e5 := e false true true
  have e6 := e true false true
  have e7 := e true true false
  have e8 := e true true true
  simp only [cfTab] at e1 e2 e3 e4 e5 e6 e7 e8
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

/-- The table selected by a boolean, as a function of bit strings: `false ↦ alphaReal`, `true ↦ betaReal`. -/
noncomputable def tabReal : Bool → BitString → ℝ
  | false => alphaReal
  | true => betaReal

/-- **One trilinear form of the two tables over a class of masks**: the cubic mask sum with the three slots
(Gram slot, acted vector, Gram slot) filled by `alphaReal`/`betaReal`, evaluated by the support-list sum. -/
theorem cubicMaskSumT_tab (P : (Fin 7 → Bool) → Prop) [DecidablePred P]
    (pN : ℕ → Prop) [DecidablePred pN] (hP : ∀ M < 128, P (maskOfNat M) ↔ pN M) (WP : ℕ)
    (hW : ∀ D < 128, ∀ E < 128, cfCount pN D E = cfWt WP D E)
    (x y w : Bool) (z : ℕ) (hz : z < 128) :
    cubicMaskSumT (tabReal x) (tabReal y) (tabReal w) (maskOfNat z) P = cfK WP z x y w := by
  rw [cubicMaskSumT_nat P pN hP _ _ _ z hz, cubNatT_eq_cubR _ _ _ _ z hz]
  have ht : ∀ b : Bool, ∀ n < 128, tabReal b (maskOfNat n) = (cfTab b n : ℝ) := by
    intro b n hn
    cases b
    · exact congrArg (fun k : ℤ => (k : ℝ)) (alphaCoefficient_maskOfNat n hn)
    · exact congrArg (fun k : ℤ => (k : ℝ)) (betaCoefficient_maskOfNat n hn)
  rw [cubR_congr _ _ (fun n => (cfTab x n : ℝ)) _ (fun n => (cfTab y n : ℝ))
    _ (fun n => (cfTab w n : ℝ)) z hz (ht x) (ht y) (ht w)]
  exact cubR_tab pN WP hW z hz x y w

end FormalResearch.FourQubitEntropy.SevenQubitIco
