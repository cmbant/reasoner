import Mathlib
import FormalResearch.QID.D5RankWitness

namespace FormalResearch.QID

abbrev Fin5V := Fin 5
abbrev Fin24V := Fin 24
abbrev Fin25V := Fin 25

/-- Twenty-five explicitly selected Type-D5 signed permutation vertices. -/
def selectedD5Cols : Fin25V → Fin5V → Fin5V :=
  ![![0, 1, 2, 3, 4],
    ![0, 1, 2, 3, 4],
    ![0, 1, 2, 3, 4],
    ![0, 1, 2, 4, 3],
    ![0, 1, 3, 2, 4],
    ![0, 1, 4, 2, 3],
    ![0, 1, 4, 3, 2],
    ![0, 2, 1, 3, 4],
    ![0, 2, 3, 1, 4],
    ![0, 2, 4, 1, 3],
    ![0, 2, 4, 3, 1],
    ![0, 3, 1, 2, 4],
    ![0, 3, 2, 1, 4],
    ![0, 4, 1, 2, 3],
    ![0, 4, 1, 3, 2],
    ![0, 4, 2, 1, 3],
    ![0, 4, 2, 3, 1],
    ![1, 0, 2, 3, 4],
    ![1, 2, 0, 3, 4],
    ![1, 2, 3, 0, 4],
    ![1, 2, 4, 3, 0],
    ![1, 4, 2, 3, 0],
    ![2, 0, 1, 3, 4],
    ![3, 0, 1, 2, 4],
    ![4, 1, 2, 0, 3]]

def selectedD5Signs : Fin25V → Fin5V → Int :=
  ![![1, -1, -1, 1, 1],
    ![1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, 1],
    ![1, -1, -1, 1, 1],
    ![1, -1, 1, -1, 1],
    ![1, -1, -1, -1, -1],
    ![1, -1, -1, -1, -1],
    ![1, 1, 1, 1, 1],
    ![1, 1, -1, -1, 1],
    ![1, 1, -1, -1, 1],
    ![1, 1, -1, -1, 1],
    ![1, -1, 1, -1, 1],
    ![1, 1, -1, -1, 1],
    ![1, -1, 1, -1, 1],
    ![1, -1, 1, -1, 1],
    ![1, -1, -1, -1, -1],
    ![1, -1, -1, -1, -1],
    ![-1, -1, -1, -1, 1],
    ![-1, 1, 1, -1, 1],
    ![-1, 1, 1, -1, 1],
    ![-1, 1, -1, -1, -1],
    ![-1, -1, -1, -1, 1],
    ![1, -1, 1, -1, 1],
    ![1, -1, 1, -1, 1],
    ![1, -1, -1, -1, -1]]

def selectedD5Vertex (k : Fin25V) : Matrix Fin5V Fin5V Int :=
  fun i j => if selectedD5Cols k i = j then selectedD5Signs k i else 0

def selectedD5NegCount (k : Fin25V) : Nat :=
  ∑ i : Fin5V, if selectedD5Signs k i = -1 then 1 else 0

def selectedD5Valid (k : Fin25V) : Prop :=
  (Finset.univ.image (selectedD5Cols k)).card = 5 ∧
  (∀ i : Fin5V, selectedD5Signs k i = 1 ∨ selectedD5Signs k i = -1) ∧
  selectedD5NegCount k % 2 = 0

def selectedD5Score (k : Fin25V) : Int :=
  ∑ i : Fin5V, selectedD5Signs k i * N5 i (selectedD5Cols k i)

/-- Every selected point is an actual Type-D5 signed-permutation Weyl vertex,
and lies on the supporting hyperplane with score five. -/
theorem selectedD5_all_active :
    ∀ k : Fin25V, selectedD5Valid k ∧ selectedD5Score k = 5 := by
  native_decide

/-- Coordinates 1,...,24 of a 5x5 matrix, dropping ambient coordinate (0,0). -/
def selectedCoord24 (V : Matrix Fin5V Fin5V Int) (q : Fin24V) : Int :=
  let n := q.val + 1
  V ⟨n / 5, by omega⟩ ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- Difference matrix from vertex 0 to vertices 1,...,24, in the 24 retained
ambient coordinates. Columns are difference vectors. -/
def selectedD5Diff24 : Matrix Fin24V Fin24V Int :=
  fun i j =>
    selectedCoord24 (selectedD5Vertex j.succ) i -
      selectedCoord24 (selectedD5Vertex 0) i

def selectedD5Diff24Mod3 : Matrix Fin24V Fin24V (ZMod 3) :=
  fun i j => (selectedD5Diff24 i j : ZMod 3)

def selectedD5Diff24InvMod3 : Matrix Fin24V Fin24V (ZMod 3) :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 2;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 2, 2, 1, 1, 0, 1, 1, 2, 2, 1, 1, 0, 1, 0, 1, 1, 2, 1, 2, 0;
      0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0;
      0, 1, 1, 1, 2, 2, 0, 1, 0, 2, 0, 2, 1, 0, 2, 0, 0, 0, 1, 1, 2, 2, 2, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 2, 2, 1, 2, 0, 1, 1, 2, 1, 1, 0, 1, 0, 0, 2, 1, 2, 1, 1, 0;
      2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0;
      0, 0, 0, 0, 2, 2, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 2, 2, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 0, 1, 0, 1, 0, 2, 2, 1, 2, 1, 0;
      0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0;
      0, 0, 0, 2, 2, 2, 1, 2, 1, 1, 1, 2, 1, 0, 0, 1, 0, 0, 1, 2, 1, 2, 2, 0;
      2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      1, 2, 2, 2, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The 24 active-vertex differences are independent: their reduction mod 3
has an explicit two-sided inverse. -/
theorem selectedD5Diff24_right_inverse :
    selectedD5Diff24Mod3 * selectedD5Diff24InvMod3 = 1 := by
  native_decide

theorem selectedD5Diff24_left_inverse :
    selectedD5Diff24InvMod3 * selectedD5Diff24Mod3 = 1 := by
  native_decide

/-- A self-contained computational certificate for the geometric content:
the score-five supporting hyperplane contains 25 explicitly specified Weyl
vertices with 24 independent affine differences. -/
theorem D5_active_affine_certificate :
    (∀ k : Fin25V, selectedD5Valid k ∧ selectedD5Score k = 5) ∧
    selectedD5Diff24Mod3 * selectedD5Diff24InvMod3 = 1 := by
  exact ⟨selectedD5_all_active, selectedD5Diff24_right_inverse⟩

end FormalResearch.QID
