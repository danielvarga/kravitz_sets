import Mathlib


namespace KravitzLP

/-- The appendix witness set for the `d = 6` LP certificate. -/
def X : List Int := [0, 2, 3, 4, 7, 8, 9, 10]

/-- Number of nontrivial atoms in the appendix LP. -/
abbrev Atom := Fin 53

/-- Number of reduced congruence constraints in the appendix LP. -/
abbrev Eqn := Fin 22

/-- The first row of the atomic matrix `T`, i.e. the indicator of atoms containing `0`. -/
def eList : List Int :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1]

/-- The reduced dual witness vector from the supplementary material. -/
def yList : List Int :=
  [2, 2, 2, 2, -2, -1, -7, -3, -2, 2, 5, -2, 1, 3, 2, -5, 2, 2, -3, -2, 2, -2]

/-- Reduced congruence matrix `C'` from the appendix, row-major. -/
def CRows : List (List Int) :=
[
  [0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1],
  [0, 1, 0, 1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 1, -1, 0, 0, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, -1, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 1, 0, 1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 1, 0, 1, -1, -1, 0, 0, 1, 0, 1, -1, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, -1, -1],
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 1, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, 0, -1, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 1, 0, 1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, -1, -1, -1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1],
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1],
  [0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1]
]

/-- Explicit nonnegative dual slack `y C' - 7 e + 2`. -/
def slackList : List Int :=
  [2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 0, 0, 1, 0, 3,
   1, 3, 3, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
   0, 0, 0, 0, 0]

/-- Accessors on finite index types. -/
def e (j : Atom) : Int :=
  eList.getD j.1 0

def y (i : Eqn) : Int :=
  yList.getD i.1 0

def C (i : Eqn) (j : Atom) : Int :=
  (CRows.getD i.1 []).getD j.1 0

def slack (j : Atom) : Int :=
  slackList.getD j.1 0

/-- The appendix data really do satisfy `slack = y*C' - 7*e + 2` entrywise. -/
theorem slack_formula (j : Atom) :
    slack j = (∑ i : Eqn, y i * C i j) - 7 * e j + 2 := by
  decide +revert

/-- Concrete verification of the dual nonnegativity condition from the appendix. -/
theorem slack_nonneg (j : Atom) : 0 ≤ slack j := by
  decide +revert

/--
A convenient LP-facing formulation.

If `x` is a feasible primal point, then the appendix dual witness forces the objective
`∑ e_j x_j` to be at most `2/7`.

This is the algebraic statement that still has to be connected to the additive-combinatorial
construction of atomic densities `a_X(ε)` from Section 2 of the paper.
-/
theorem lp_bound_from_dual
    (x : Atom → ℚ)
    (hx_nonneg : ∀ j, 0 ≤ x j)
    (hx_sum : (∑ j : Atom, x j) = 1)
    (hx_congr : ∀ i : Eqn, (∑ j : Atom, (C i j : ℚ) * x j) = 0) :
    (∑ j : Atom, (e j : ℚ) * x j) ≤ (2 : ℚ) / 7 := by
  have hslack :
      0 ≤ ∑ j : Atom, ((slack j : ℚ) * x j) := by
    refine Finset.sum_nonneg ?_
    intro j _
    exact mul_nonneg (by exact_mod_cast slack_nonneg j) (hx_nonneg j)
  have hrewrite :
      ∑ j : Atom, ((slack j : ℚ) * x j)
        = ∑ j : Atom, (((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) - 7 * (e j : ℚ) + 2) * x j) := by
    congr with j
    rw [slack_formula]
    norm_num
  rw [hrewrite] at hslack
  have hcongr_collapse :
      ∑ j : Atom, ((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) * x j)
        = ∑ i : Eqn, (y i : ℚ) * (∑ j : Atom, (C i j : ℚ) * x j) := by
    calc
      ∑ j : Atom, ((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) * x j)
          = ∑ j : Atom, ∑ i : Eqn, ((y i : ℚ) * (C i j : ℚ)) * x j := by
              simp_rw [Finset.sum_mul]
      _ = ∑ j : Atom, ∑ i : Eqn, (y i : ℚ) * ((C i j : ℚ) * x j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            ring_nf
      _ = ∑ i : Eqn, ∑ j : Atom, (y i : ℚ) * ((C i j : ℚ) * x j) := by
            rw [Finset.sum_comm]
      _ = ∑ i : Eqn, (y i : ℚ) * (∑ j : Atom, (C i j : ℚ) * x j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← Finset.mul_sum]
  have hcollapse :
      ∑ j : Atom, (((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) - 7 * (e j : ℚ) + 2) * x j)
        = -7 * (∑ j : Atom, (e j : ℚ) * x j) + 2 := by
    calc
      ∑ j : Atom, (((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) - 7 * (e j : ℚ) + 2) * x j)
          = ∑ j : Atom,
              (((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) * x j)
                + (-7 : ℚ) * ((e j : ℚ) * x j)
                + (2 : ℚ) * x j) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = (∑ j : Atom, ((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) * x j))
              + (∑ j : Atom, (-7 : ℚ) * ((e j : ℚ) * x j))
              + (∑ j : Atom, (2 : ℚ) * x j) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ j : Atom, ((∑ i : Eqn, (y i : ℚ) * (C i j : ℚ)) * x j))
              - 7 * (∑ j : Atom, (e j : ℚ) * x j)
              + 2 * (∑ j : Atom, x j) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
            ring
      _ = (∑ i : Eqn, (y i : ℚ) * (∑ j : Atom, (C i j : ℚ) * x j))
              - 7 * (∑ j : Atom, (e j : ℚ) * x j)
              + 2 * (∑ j : Atom, x j) := by
            rw [hcongr_collapse]
      _ = -7 * (∑ j : Atom, (e j : ℚ) * x j) + 2 * (∑ j : Atom, x j) := by
            simp [hx_congr]
      _ = -7 * (∑ j : Atom, (e j : ℚ) * x j) + 2 := by simp [hx_sum]
  rw [hcollapse] at hslack
  linarith

end KravitzLP
