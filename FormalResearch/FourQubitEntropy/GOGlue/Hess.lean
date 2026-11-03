module

public import FormalResearch.FourQubitEntropy.GOGlue.Target

/-!
# GO glue: the height Hessian as a polynomial matrix

`pHess l m : PQ 1` transcribes `sHess` of `PaperEGoSlice.lean`: the generators `gens` act on the constant
pair `cStar` by integer matrices (`GenZ`, computed by Lean), and `sHess v l m` is
`-3/2 ⟨X, hx_{lm}⟩ - 1/2 ⟨Y, hy_{lm}⟩` with `hx, hy` the (integer) symmetrised double actions.
`pHess_rel : Rel x pHess (sHess (restr x))`.  Claim class: proved.
-/

@[expose] public section


open Finset
open scoped Matrix

namespace FormalResearch.FourQubitEntropy.GO
open GOProbe GOProbe.PQ

abbrev M4Z := Matrix (Fin 4) (Fin 4) ℤ

structure GenZ where
  L : M4Z
  R : M4Z
  p : ℤ

def skewGZ (i j : Fin 4) : M4Z :=
  Matrix.of fun a b => if a = i ∧ b = j then 1 else if a = j ∧ b = i then -1 else 0

def zsm (c : ℤ) (A : M4Z) : M4Z := Matrix.of fun i j => c * A i j

def GenZ.act (g : GenZ) (xy : M4Z × M4Z) : M4Z × M4Z :=
  (g.L * xy.1 - xy.1 * g.R - zsm g.p xy.2, g.L * xy.2 - xy.2 * g.R + zsm (3 * g.p) xy.1)

def gensZ : Fin 10 → GenZ := ![
  ⟨skewGZ 0 1, 0, 0⟩, ⟨0, skewGZ 0 1, 0⟩, ⟨skewGZ 0 2, 0, 0⟩, ⟨0, skewGZ 0 2, 0⟩,
  ⟨skewGZ 0 3, 0, 0⟩, ⟨0, skewGZ 0 3, 0⟩,
  ⟨skewGZ 1 2, 0, 0⟩, ⟨skewGZ 1 3, 0, 0⟩, ⟨skewGZ 2 3, 0, 0⟩, ⟨0, 0, 1⟩]

def cStarZ : M4Z × M4Z :=
  (Matrix.of fun a b => if a = 0 ∧ b = 0 then 1 else 0,
   Matrix.of fun a b => if a = b ∧ a ≠ 0 then 1 else 0)

def hxz (l m : Fin 10) (i j : Fin 4) : ℤ :=
  ((gensZ l).act ((gensZ m).act cStarZ)).1 i j + ((gensZ m).act ((gensZ l).act cStarZ)).1 i j

def hyz (l m : Fin 10) (i j : Fin 4) : ℤ :=
  ((gensZ l).act ((gensZ m).act cStarZ)).2 i j + ((gensZ m).act ((gensZ l).act cStarZ)).2 i j

/-- `-3/2 ⟨X, hx⟩ - 1/2 ⟨Y, hy⟩`. -/
def pHess (l m : Fin 10) : PQ 1 :=
  add (sumF fun i => sumF fun j => smul ((-3 / 2 : ℚ) * (hxz l m i j : ℚ)) (pX i j))
    (sumF fun i => sumF fun j => smul ((-1 / 2 : ℚ) * (hyz l m i j : ℚ)) (pY i j))

noncomputable section

def GenZ.toGen (g : GenZ) : Gen := ⟨g.L.map (Int.cast : ℤ → ℝ), g.R.map (Int.cast : ℤ → ℝ), g.p⟩

theorem gens_eq (l : Fin 10) : gens l = (gensZ l).toGen := by
  have h0 : ∀ i j : Fin 4, skewG i j = (skewGZ i j).map (Int.cast : ℤ → ℝ) := by
    intro i j
    ext a b
    simp only [skewG, skewGZ, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> simp
  fin_cases l <;> simp [gens, gensZ, GenZ.toGen, h0]

def mapPair (xy : M4Z × M4Z) : Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ :=
  (xy.1.map (Int.cast : ℤ → ℝ), xy.2.map (Int.cast : ℤ → ℝ))

theorem act_cast (g : GenZ) (xy : M4Z × M4Z) : g.toGen.act (mapPair xy) = mapPair (g.act xy) := by
  unfold Gen.act GenZ.act mapPair GenZ.toGen zsm
  refine Prod.ext ?_ ?_ <;> ext i j <;>
    simp [Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Fin.sum_univ_four] 

theorem cStar_eq : cStar = mapPair cStarZ := by
  unfold cStar cStarZ mapPair
  refine Prod.ext ?_ ?_ <;> ext a b <;> simp

theorem sHess_eq (x : ℕ → ℝ) (l m : Fin 10) :
    sHess (restr x) l m = (-3 / 2 : ℝ) * (∑ i, ∑ j, (hxz l m i j : ℝ) * sX (restr x) i j) +
      (-1 / 2 : ℝ) * (∑ i, ∑ j, (hyz l m i j : ℝ) * sY (restr x) i j) := by
  have e1 : ∀ l m : Fin 10, ((gens l).act ((gens m).act cStar)) =
      mapPair ((gensZ l).act ((gensZ m).act cStarZ)) := by
    intro l m
    rw [gens_eq, gens_eq, cStar_eq, act_cast, act_cast]
  unfold sHess
  simp only [e1, mapPair, Matrix.map_apply, hxz, hyz]
  have key : ∀ (U V : M4Z) (W : Matrix (Fin 4) (Fin 4) ℝ),
      ∑ i, ∑ j, W i j * ((U i j : ℝ) / 2 + (V i j : ℝ) / 2) =
        (1 / 2) * ∑ i, ∑ j, ((U i j + V i j : ℤ) : ℝ) * W i j := by
    intro U V W
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [key, key]
  ring

end


section Sound3
variable (x : ℕ → ℝ)

theorem pHess_rel : Rel x (fun l m : Fin 10 => pHess l m) (Matrix.of (sHess (restr x))) := by
  intro l m
  rw [Matrix.of_apply, sHess_eq]
  have hX := rel_pX x
  have hY := rel_pY x
  simp only [pHess, val_add, val_sumF, val_smul, hX _ _, hY _ _, hxz, hyz]
  simp only [Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_ <;>
    push_cast <;> ring

end Sound3

end FormalResearch.FourQubitEntropy.GO
