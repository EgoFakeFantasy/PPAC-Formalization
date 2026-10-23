import PPAC.Migration.Internal.OriginalArgumentCandidateValue

/-! 全部内部索引上的原Run₁字段对应及原Run₂字段正确性归纳属性。 -/
namespace PPAC.Migration.Internal.OriginalArgumentFieldSyntax
open Source SourceAlgebra SourceLogic
open StructuralListFieldSyntax (field field_rename)
open SyntaxRenameQuerySyntax (of_eq)

def fields {m} (w mode depth parameter k n q : Fin m) : Formula m := .all (.all (.all
  (((Formula.mem (Fin.last m).castSucc.castSucc k.castSucc.castSucc.castSucc).conj
    ((field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (field w.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))))).imp
        (OriginalTransformRowSyntax.run 1 w.castSucc.castSucc.castSucc mode.castSucc.castSucc.castSucc depth.castSucc.castSucc.castSucc parameter.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))))

def property {m} (w mode depth parameter a b n : Fin m) : Formula m := .all (.all
  ((SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc).imp
    ((OriginalTransformRowSyntax.run 2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (fields w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1))))))

def earlier {m} (w mode depth parameter a b n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc (Fin.last m))))

theorem fields_rename {m j} (w mode depth parameter k n q : Fin m) (ρ : Fin m → Fin j) :
    (fields w mode depth parameter k n q).rename ρ = fields (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ k) (ρ n) (ρ q) := by
  simp only [fields, Formula.rename, field_rename, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_rename {m j} (w mode depth parameter a b n : Fin m) (ρ : Fin m → Fin j) :
    (property w mode depth parameter a b n).rename ρ = property (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ n) := by
  simp only [property, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, OriginalTransformRowSyntax.run_rename, fields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m j} (w mode depth parameter a b n : Fin m) (ρ : Fin m → Fin j) :
    (earlier w mode depth parameter a b n).rename ρ = earlier (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fields_at {m} {Γ : Context m} (w mode depth parameter k n q i x y : Fin m)
    (hf : Derives Γ (fields w mode depth parameter k n q)) (hi : Derives Γ (.mem i k))
    (hx : Derives Γ (field w n i x)) (hy : Derives Γ (field w q i y)) : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter x y) := by
  have he : Derives Γ (((Formula.mem i k).conj ((field w n i x).conj (field w q i y))).imp (OriginalTransformRowSyntax.run 1 w mode depth parameter x y)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, field_rename, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE y (Derives.allE x (Derives.allE i hf)))
  exact .impE he (.conjI hi (.conjI hx hy))

theorem property_at {m} {Γ : Context m} (w mode depth parameter a b n k q : Fin m)
    (hp : Derives Γ (property w mode depth parameter a b n)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n q)) : Derives Γ (fields w mode depth parameter k n q) := by
  have hi : Derives Γ ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).imp (fields w mode depth parameter k n q))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, OriginalTransformRowSyntax.run_rename, fields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE q (Derives.allE k hp))
  exact .impE (.impE hi hL) hr

theorem earlier_at {m} {Γ : Context m} (w mode depth parameter a b n t : Fin m)
    (he : Derives Γ (earlier w mode depth parameter a b n)) (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n)) : Derives Γ (property w mode depth parameter a b t) := by
  have hi : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w mode depth parameter a b t))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t he)
  exact .impE (.impE hi ht) htn

end PPAC.Migration.Internal.OriginalArgumentFieldSyntax
