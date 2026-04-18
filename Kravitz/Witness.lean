import Kravitz.KravitzLP

open scoped BigOperators

namespace KravitzLP

/-- The witness set used in the LP certificate. -/
def witnessPoint : Fin 8 → Int
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 7
  | 5 => 8
  | 6 => 9
  | 7 => 10

/-- The 53 allowed atoms, encoded as subsets of the 8-point witness set. -/
def atomSupports : List (List (Fin 8)) :=
  [
    [],
    [7],
    [6],
    [6, 7],
    [5],
    [5, 7],
    [5, 6],
    [5, 6, 7],
    [4],
    [4, 6],
    [4, 5],
    [4, 5, 6],
    [3],
    [3, 6],
    [3, 5],
    [3, 5, 6],
    [2],
    [2, 7],
    [2, 5],
    [2, 5, 7],
    [2, 4],
    [2, 4, 5],
    [2, 3],
    [1],
    [1, 7],
    [1, 6],
    [1, 6, 7],
    [1, 4],
    [1, 4, 6],
    [1, 3],
    [1, 3, 6],
    [1, 2],
    [1, 2, 3],
    [0],
    [0, 7],
    [0, 6],
    [0, 6, 7],
    [0, 5],
    [0, 5, 7],
    [0, 5, 6],
    [0, 5, 6, 7],
    [0, 4],
    [0, 4, 6],
    [0, 4, 5],
    [0, 4, 5, 6],
    [0, 3],
    [0, 3, 6],
    [0, 3, 5],
    [0, 3, 5, 6],
    [0, 1],
    [0, 1, 6],
    [0, 1, 4],
    [0, 1, 4, 6]
  ]

/-- The reduced congruence data from the supplementary material, on atom supports. -/
def congrLeftSupports : List (List (Fin 8)) :=
  [
    [7],
    [7],
    [7],
    [7],
    [7],
    [7],
    [7],
    [6, 7],
    [6, 7],
    [6, 7],
    [6, 7],
    [5, 7],
    [5, 7],
    [5, 7],
    [5, 6, 7],
    [5, 6, 7],
    [3, 6],
    [3, 5],
    [3, 5, 6],
    [2, 7],
    [2, 5, 7],
    [1, 3, 6]
  ]

/-- The reduced congruence data from the supplementary material, on atom supports. -/
def congrRightSupports : List (List (Fin 8)) :=
  [
    [6],
    [5],
    [4],
    [3],
    [2],
    [1],
    [0],
    [5, 6],
    [4, 5],
    [2, 3],
    [1, 2],
    [4, 6],
    [1, 3],
    [0, 1],
    [4, 5, 6],
    [1, 2, 3],
    [2, 5],
    [2, 4],
    [2, 4, 5],
    [1, 6],
    [1, 4, 6],
    [0, 1, 4]
  ]

/-- The translation amounts witnessing the reduced congruences. -/
def congrShifts : List Int :=
  [-1, -2, -3, -6, -7, -8, -10, -1, -2, -6, -7, -1, -6, -8, -1, -6, -1, -1, -1, -1, -1, -2]

private theorem atomSupports_length : atomSupports.length = 53 := by native_decide
private theorem congrLeftSupports_length : congrLeftSupports.length = 22 := by native_decide
private theorem congrRightSupports_length : congrRightSupports.length = 22 := by native_decide
private theorem congrShifts_length : congrShifts.length = 22 := by native_decide

/-- The support of an LP atom, viewed as a subset of the witness set. -/
def atomSupport (j : Atom) : Finset (Fin 8) :=
  (atomSupports.getD j.1 []).toFinset

/-- The left-hand side of a reduced congruence, viewed as a subset of the witness set. -/
def congrLeftSupport (i : Eqn) : Finset (Fin 8) :=
  (congrLeftSupports.getD i.1 []).toFinset

/-- The right-hand side of a reduced congruence, viewed as a subset of the witness set. -/
def congrRightSupport (i : Eqn) : Finset (Fin 8) :=
  (congrRightSupports.getD i.1 []).toFinset

/-- The translation amount witnessing a reduced congruence. -/
def congrShift (i : Eqn) : Int :=
  congrShifts.getD i.1 0

/-- A subset of the witness set is admissible if it does not realize the forbidden value `6`. -/
def ForbiddenFree (S : Finset (Fin 8)) : Prop :=
  ∀ i j k : Fin 8, i ∈ S → j ∈ S → k ∈ S →
    witnessPoint i + witnessPoint j - 2 * witnessPoint k ≠ 6

instance instDecidableForbiddenFree (S : Finset (Fin 8)) : Decidable (ForbiddenFree S) := by
  unfold ForbiddenFree
  infer_instance

theorem atomSupport_forbiddenFree (j : Atom) : ForbiddenFree (atomSupport j) := by
  fin_cases j <;> native_decide

theorem atomSupport_injective : Function.Injective atomSupport := by
  native_decide

theorem forbiddenFree_univ_eq_image :
    (Finset.univ.filter ForbiddenFree : Finset (Finset (Fin 8)))
      = Finset.univ.image atomSupport := by
  native_decide

/-- The explicit witness set agrees with the support-based interpretation of `e`. -/
theorem e_eq_indicator (j : Atom) :
    e j = if (0 : Fin 8) ∈ atomSupport j then 1 else 0 := by
  fin_cases j <;> native_decide

/-- The explicit witness matrix agrees with the support-based interpretation of `C`. -/
theorem C_eq_support_difference (i : Eqn) (j : Atom) :
    C i j =
      (if congrLeftSupport i ⊆ atomSupport j then 1 else 0)
        - (if congrRightSupport i ⊆ atomSupport j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> native_decide

/-- The reduced congruence data are genuinely translates inside the witness set. -/
theorem congr_translate_spec (i : Eqn) :
    (congrRightSupport i).image witnessPoint
      = (congrLeftSupport i).image fun k => witnessPoint k + congrShift i := by
  fin_cases i <;> native_decide

end KravitzLP
