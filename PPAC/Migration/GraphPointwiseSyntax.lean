import PPAC.Migration.GraphFamilySyntax

/-! 原图边关系的包含/等价；使用既有跨图输出相容关系。 -/
namespace PPAC.Migration.GraphPointwiseSyntax
open Source SourceAlgebra SourceLogic GraphSyntax GraphFamilySyntax

def edgeIncluded {m} (f g : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def sameEdges {m} (f g : Fin m) : Formula m := (edgeIncluded f g).conj (edgeIncluded g f)

theorem edgeIncluded_rename {m k} (f g : Fin m) (r : Fin m → Fin k) :
    (edgeIncluded f g).rename r = edgeIncluded (r f) (r g) := by
  simp only [edgeIncluded, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem sameEdges_rename {m k} (f g : Fin m) (r : Fin m → Fin k) :
    (sameEdges f g).rename r = sameEdges (r f) (r g) := by
  simp only [sameEdges, Formula.rename, edgeIncluded_rename]

theorem edgeIncluded_at {m} {Γ : Context m} (f g x y : Fin m) (h : Derives Γ (edgeIncluded f g)) :
    Derives Γ ((edge f x y).imp (edge g x y)) := by
  have hi := Derives.allE y (Derives.allE x h)
  simpa only [Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem edge_subst_output {m} {Γ : Context m} (f x y z : Fin m)
    (he : Derives Γ (.equal y z)) (hy : Derives Γ (edge f x y)) : Derives Γ (edge f x z) := by
  have hi : Derives Γ ((edge f.castSucc x.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have h := Derives.eqSubst (edge f.castSucc x.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem agrees_symm {m} {Γ : Context m} (f g : Fin m) (ha : Derives Γ (agrees f g)) : Derives Γ (agrees g f) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have ha' : Derives (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
      (agrees f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, agrees_rename] using
      Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha))
  apply Derives.impI
  apply Derives.impI
  exact eq_symm (.impE (.impE (add (add (agrees_at f.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc ha') _) _)
    (.hyp (Or.inl rfl))) (.hyp (Or.inr (Or.inl rfl))))
end PPAC.Migration.GraphPointwiseSyntax
