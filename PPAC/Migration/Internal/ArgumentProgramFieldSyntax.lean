import PPAC.Migration.Internal.OriginalArgumentFieldInduction

/-! 独立项程序的全部内部字段像规格；定义不调用原列表Run₂或旧列表变换算子。 -/
namespace PPAC.Migration.Internal.ArgumentProgramFieldSyntax
open Source SourceAlgebra SourceLogic
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

def fields {m} (w R S k n q : Fin m) : Formula m := .all (.all (.all
  (((Formula.mem (Fin.last m).castSucc.castSucc k.castSucc.castSucc.castSucc).conj
    ((field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (field w.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))))).imp
        (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc S.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))))

def mapped {m} (w R S k c d n q : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termList w k c d q).conj (fields w R S k n q)

theorem fields_rename {m j} (w R S k n q : Fin m) (ρ : Fin m → Fin j) :
    (fields w R S k n q).rename ρ = fields (ρ w) (ρ R) (ρ S) (ρ k) (ρ n) (ρ q) := by
  simp only [fields, Formula.rename, field_rename, TermTransformProgramSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem mapped_rename {m j} (w R S k c d n q : Fin m) (ρ : Fin m → Fin j) :
    (mapped w R S k c d n q).rename ρ = mapped (ρ w) (ρ R) (ρ S) (ρ k) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [mapped, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, fields_rename]

theorem fields_at {m} {Γ : Context m} (w R S k n q i x y : Fin m)
    (hf : Derives Γ (fields w R S k n q)) (hi : Derives Γ (.mem i k))
    (hx : Derives Γ (field w n i x)) (hy : Derives Γ (field w q i y)) :
    Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S x y) := by
  have he : Derives Γ (((Formula.mem i k).conj ((field w n i x).conj (field w q i y))).imp (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S x y)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, field_rename, TermTransformProgramSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE y (Derives.allE x (Derives.allE i hf)))
  exact .impE he (.conjI hi (.conjI hx hy))

end PPAC.Migration.Internal.ArgumentProgramFieldSyntax
