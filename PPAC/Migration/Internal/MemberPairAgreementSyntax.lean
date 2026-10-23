import PPAC.Migration.Internal.MemberProgramSyntax

/-! 两参数原Run₂与独立程序的全内部比较前提；随后由具体mode0／3原核证明消去。 -/
namespace PPAC.Migration.Internal.MemberPairAgreementSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def agreement {m} (w mode depth parameter R S c d x y : Fin m) : Formula m := .all (.all
  ((SyntaxForestSyntax.forest 2 w.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc) (Fin.last m).castSucc).imp
    ((OriginalTransformRowSyntax.run 2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (ArgumentPairProgramSyntax.returned w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))))))

theorem agreement_rename {m j} (w mode depth parameter R S c d x y : Fin m) (ρ : Fin m → Fin j) :
    (agreement w mode depth parameter R S c d x y).rename ρ = agreement (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ R) (ρ S) (ρ c) (ρ d) (ρ x) (ρ y) := by
  simp only [agreement, Formula.rename, Formula.iff, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, OriginalTransformRowSyntax.run_rename, ArgumentPairProgramSyntax.returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem agreement_at {m} {Γ : Context m} (w mode depth parameter R S c d x y A Q : Fin m)
    (hh : Derives Γ (agreement w mode depth parameter R S c d x y))
    (hf : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) A)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter A Q).iff (ArgumentPairProgramSyntax.returned w R S c d x y Q)) := by
  have ha := Derives.allE Q (Derives.allE A hh)
  have he : Derives Γ ((SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) A).imp
      ((OriginalTransformRowSyntax.run 2 w mode depth parameter A Q).iff (ArgumentPairProgramSyntax.returned w R S c d x y Q))) := by
    simpa only [agreement, Formula.instantiate, Formula.rename, Formula.iff, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map, OriginalTransformRowSyntax.run_rename, ArgumentPairProgramSyntax.returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ha
  exact .impE he hf

end PPAC.Migration.Internal.MemberPairAgreementSyntax
