import PPAC.Migration.Internal.ProjectBoundShiftExistence

/-! Actual pure-code template for the original Project subset atom. -/
namespace PPAC.Migration.Internal.ProjectSubsetSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def matrix {m} (w b z x y q : Fin m) (env : Fin 8 → Fin m) : Formula m :=
  (successor (env 0) b).conj
    ((ProjectBoundShiftSyntax.shifted w x (env 1)).conj
      ((ProjectBoundShiftSyntax.shifted w y (env 2)).conj
        ((SyntaxVariableSyntax.code true w z (env 3)).conj
          ((SyntaxAtomSyntax.zeroScalar w (env 4)).conj
            ((SyntaxAtomSyntax.memberCode w (env 4) (env 3) (env 1) (env 5)).conj
              ((SyntaxAtomSyntax.memberCode w (env 4) (env 3) (env 2) (env 6)).conj
                ((SyntaxLogicalSyntax.binaryCode 2 w (env 5) (env 6) (env 7)).conj
                  (SyntaxLogicalSyntax.singleCode 9 w (env 7) q))))))))

def body {m} (w b z x y q : Fin m) : Formula (m+8) :=
  matrix (old 8 w) (old 8 b) (old 8 z) (old 8 x) (old 8 y) (old 8 q) (slot 8)

def expanded {m} (w b z x y q : Fin m) : Formula m := existsMany 8 (body w b z x y q)

def existsOutput {m} (w b z x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (expanded w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m)))

def uniqueOutput {m} (w b z x y q : Fin m) : Formula m := .all
  ((expanded w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def fiber {m} (w b z x y : Fin m) : Formula m := .ex
  ((((Formula.mem (Fin.last m) w.castSucc).conj (expanded w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m))).conj
    (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)).conj
      (uniqueOutput w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m)))

theorem matrix_rename {m l} (w b z x y q : Fin m) (env : Fin 8 → Fin m) (ρ : Fin m → Fin l) :
    (matrix w b z x y q env).rename ρ = matrix (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ q) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, successor_rename, ProjectBoundShiftSyntax.shifted_rename,
    SyntaxVariableSyntax.code_rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename,
    SyntaxLogicalSyntax.binaryCode_rename, SyntaxLogicalSyntax.singleCode_rename]

theorem body_lift {m l} (w b z x y q : Fin m) (ρ : Fin m → Fin l) :
    (body w b z x y q).rename (lift 8 ρ) = body (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ q) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem expanded_rename {m l} (w b z x y q : Fin m) (ρ : Fin m → Fin l) :
    (expanded w b z x y q).rename ρ = expanded (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ q) := by
  simp only [expanded, existsMany_rename, body_lift]

theorem existsOutput_rename {m l} (w b z x y : Fin m) (ρ : Fin m → Fin l) :
    (existsOutput w b z x y).rename ρ = existsOutput (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) := by
  simp only [existsOutput, Formula.rename, expanded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m l} (w b z x y q : Fin m) (ρ : Fin m → Fin l) :
    (uniqueOutput w b z x y q).rename ρ = uniqueOutput (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, expanded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (w b z x y : Fin m) (ρ : Fin m → Fin l) :
    (fiber w b z x y).rename ρ = fiber (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) := by
  simp only [fiber, Formula.rename, expanded_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_expanded {m} {Γ : Context m} (w b z x y q : Fin m) (env : Fin 8 → Fin m)
    (hm : Derives Γ (matrix w b z x y q env)) : Derives Γ (expanded w b z x y q) := by
  apply HornBinderRules.intro_many 8 (body w b z x y q) env
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm

theorem intro_exists {m} {Γ : Context m} (w b z x y q : Fin m) (hq : Derives Γ (.mem q w))
    (he : Derives Γ (expanded w b z x y q)) : Derives Γ (existsOutput w b z x y) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, expanded_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq he)

end PPAC.Migration.Internal.ProjectSubsetSyntax
