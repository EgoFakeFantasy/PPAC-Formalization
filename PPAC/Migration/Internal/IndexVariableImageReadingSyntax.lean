import PPAC.Migration.Internal.IndexVariableTermReading

/-! 索引图与变量项像图的全内部逐边读取合同，不以宿主回调表示表。 -/
namespace PPAC.Migration.Internal.IndexVariableImageReadingSyntax
open Source SourceAlgebra SourceLogic

def point {m} (isBound : Bool) (w r f i j q : Fin m) : Formula m :=
  (GraphSyntax.edge r i j).imp ((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code isBound w j q))

def reads {m} (isBound : Bool) (w r f : Fin m) : Formula m := .all (.all (.all
  (point isBound w.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))

theorem point_rename {m k} (isBound : Bool) (w r f i j q : Fin m) (ρ : Fin m → Fin k) :
    (point isBound w r f i j q).rename ρ = point isBound (ρ w) (ρ r) (ρ f) (ρ i) (ρ j) (ρ q) := by
  simp only [point, Formula.iff, Formula.rename, GraphSyntax.edge_rename, SyntaxVariableSyntax.code_rename]

theorem reads_rename {m k} (isBound : Bool) (w r f : Fin m) (ρ : Fin m → Fin k) :
    (reads isBound w r f).rename ρ = reads isBound (ρ w) (ρ r) (ρ f) := by
  simp only [reads, Formula.rename, point_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem at_indices {m} {Γ : Context m} (isBound : Bool) (w r f i j q : Fin m)
    (hr : Derives Γ (reads isBound w r f)) : Derives Γ (point isBound w r f i j q) :=
  SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, point_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE q (Derives.allE j (Derives.allE i hr)))

end PPAC.Migration.Internal.IndexVariableImageReadingSyntax
