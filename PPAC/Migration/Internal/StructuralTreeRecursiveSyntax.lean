import PPAC.Migration.Internal.StructuralTreeHistory

/-! 树求值的递归子字段条件；接受/拒绝是实际内部求值在真实单位/零处的值。 -/
namespace PPAC.Migration.Internal.StructuralTreeRecursiveSyntax
open Source SourceAlgebra SourceLogic GraphSyntax StructuralTreeEvaluationSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)

def acceptedChildren {m} (w z e f : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (evaluation w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1)) e.castSucc.castSucc)))

def branchBody {m} (w z e n : Fin m) : Formula (m+4) :=
  (shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).conj
    (acceptedChildren w.castSucc.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)))

def branch {m} (w z e n : Fin m) : Formula m := .ex (.ex (.ex (.ex (branchBody w z e n))))

def accepts {m} (w z e n : Fin m) : Formula m := evaluation w z e n e

def rejects {m} (w z e n : Fin m) : Formula m := evaluation w z e n z

theorem acceptedChildren_rename {m k} (w z e f : Fin m) (s : Fin m → Fin k) : (acceptedChildren w z e f).rename s = acceptedChildren (s w) (s z) (s e) (s f) := by
  simp only [acceptedChildren, Formula.rename, edge_rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem branch_rename {m k} (w z e n : Fin m) (s : Fin m → Fin k) : (branch w z e n).rename s = branch (s w) (s z) (s e) (s n) := by
  simp only [branch, branchBody, Formula.rename, shape_rename, acceptedChildren_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem accepts_rename {m k} (w z e n : Fin m) (s : Fin m → Fin k) : (accepts w z e n).rename s = accepts (s w) (s z) (s e) (s n) := evaluation_rename w z e n e s

theorem rejects_rename {m k} (w z e n : Fin m) (s : Fin m → Fin k) : (rejects w z e n).rename s = rejects (s w) (s z) (s e) (s n) := evaluation_rename w z e n z s

theorem accepted_at {m} {Γ : Context m} (w z e f i y : Fin m) (ha : Derives Γ (acceptedChildren w z e f))
    (he : Derives Γ (edge f i y)) : Derives Γ (evaluation w z e y e) := by
  have h : Derives Γ ((edge f i y).imp (evaluation w z e y e)) := by
    simpa only [acceptedChildren, Formula.instantiate, Formula.rename, edge_rename, evaluation_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i ha)
  exact .impE h he

theorem intro_branch {m} {Γ : Context m} (w z e n tag p l f : Fin m) (hs : Derives Γ (shape w n tag p l f))
    (ha : Derives Γ (acceptedChildren w z e f)) : Derives Γ (branch w z e n) := by
  apply Derives.exI tag
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI f
  simp only [branchBody, Formula.instantiate, Formula.rename, shape_rename, acceptedChildren_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs ha

theorem eliminate_branch {m} {Γ : Context m} (w z e n : Fin m) (q : Formula m) (hb : Derives Γ (branch w z e n))
    (hc : Derives (Context.add (branchBody w z e n) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) q.raise.raise.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (.ex (.ex _)))) at hb
  apply Derives.exE hb
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩
end PPAC.Migration.Internal.StructuralTreeRecursiveSyntax
