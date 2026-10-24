import PPAC.Migration.Internal.ProjectSubsetSyntax

/-! Fixed constructor assembly; all code arguments remain arbitrary internal objects. -/
namespace PPAC.Migration.Internal.ProjectSubsetAssembly
open Source SourceAlgebra SourceLogic OmegaSyntax

def environment {m} (B X Y V S L R P : Fin m) (i : Fin 8) : Fin m :=
  match i.val with
  | 0 => B | 1 => X | 2 => Y | 3 => V | 4 => S | 5 => L | 6 => R | _ => P

theorem assemble {m} {Γ : Context m} (w b z x y B X Y V S L R P q : Fin m)
    (hB : Derives Γ (successor B b)) (hX : Derives Γ (ProjectBoundShiftSyntax.shifted w x X))
    (hY : Derives Γ (ProjectBoundShiftSyntax.shifted w y Y)) (hV : Derives Γ (SyntaxVariableSyntax.code true w z V))
    (hS : Derives Γ (SyntaxAtomSyntax.zeroScalar w S)) (hL : Derives Γ (SyntaxAtomSyntax.memberCode w S V X L))
    (hR : Derives Γ (SyntaxAtomSyntax.memberCode w S V Y R)) (hP : Derives Γ (SyntaxLogicalSyntax.binaryCode 2 w L R P))
    (hq : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w P q)) : Derives Γ (ProjectSubsetSyntax.expanded w b z x y q) := by
  have hm : Derives Γ (ProjectSubsetSyntax.matrix w b z x y q (environment B X Y V S L R P)) :=
    .conjI hB (.conjI hX (.conjI hY (.conjI hV (.conjI hS (.conjI hL (.conjI hR (.conjI hP hq)))))))
  exact ProjectSubsetSyntax.intro_expanded w b z x y q (environment B X Y V S L R P) hm

end PPAC.Migration.Internal.ProjectSubsetAssembly
