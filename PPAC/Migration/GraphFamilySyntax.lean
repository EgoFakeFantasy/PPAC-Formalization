import PPAC.Migration.GraphDomainAlgebra

/-! 任意内部图集合族、相容性及并图结果的纯对象公式。 -/
namespace PPAC.Migration.GraphFamilySyntax
open Source SourceAlgebra GraphSyntax InsertSyntax GraphDomainSyntax

def isGraph {m} (f : Fin m) : Formula m := .ex (functionOn f.castSucc (Fin.last m))

def graphs {m} (f : Fin m) : Formula m := .all ((Formula.mem (Fin.last m) f.castSucc).imp (isGraph (Fin.last m)))

def agrees {m} (f h : Fin m) : Formula m :=
  .all (.all (.all ((edge f.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).imp
    ((edge h.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).imp
      (.equal (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

def compatible {m} (f : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)) f.castSucc.castSucc).imp (agrees (Fin.last m).castSucc (Fin.last (m+1))))))

def memberEdge {m} (f x y : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) f.castSucc).conj (edge (Fin.last m) x.castSucc y.castSucc))

def edgeLaw {m} (g f : Fin m) : Formula m :=
  .all (.all ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    (memberEdge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def witness {m} (g d f : Fin m) : Formula m :=
  (unionOf g f).conj ((domain d g).conj ((functionOn g d).conj (edgeLaw g f)))

def existsUnion {m} (f : Fin m) : Formula m :=
  .ex (.ex (witness (Fin.last m).castSucc (Fin.last (m+1)) f.castSucc.castSucc))

theorem isGraph_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (isGraph f).rename r = isGraph (r f) := by
  simp only [isGraph, Formula.rename, functionOn_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphs_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (graphs f).rename r = graphs (r f) := by
  simp only [graphs, Formula.rename, isGraph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem agrees_rename {m k} (f h : Fin m) (r : Fin m → Fin k) :
    (agrees f h).rename r = agrees (r f) (r h) := by
  simp only [agrees, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem compatible_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (compatible f).rename r = compatible (r f) := by
  simp only [compatible, Formula.rename, agrees_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem memberEdge_rename {m k} (f x y : Fin m) (r : Fin m → Fin k) :
    (memberEdge f x y).rename r = memberEdge (r f) (r x) (r y) := by
  simp only [memberEdge, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem edgeLaw_rename {m k} (g f : Fin m) (r : Fin m → Fin k) :
    (edgeLaw g f).rename r = edgeLaw (r g) (r f) := by
  simp only [edgeLaw, Formula.iff, Formula.rename, edge_rename, memberEdge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem witness_rename {m k} (g d f : Fin m) (r : Fin m → Fin k) :
    (witness g d f).rename r = witness (r g) (r d) (r f) := by
  simp only [witness, Formula.rename, unionOf_rename, domain_rename, functionOn_rename, edgeLaw_rename]

theorem existsUnion_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (existsUnion f).rename r = existsUnion (r f) := by
  simp only [existsUnion, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphs_at {m} {Γ : Context m} (f h : Fin m) (hf : Derives Γ (graphs f)) :
    Derives Γ ((Formula.mem h f).imp (isGraph h)) := by
  have hi := Derives.allE h hf
  simpa only [Formula.instantiate, Formula.rename, isGraph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem compatible_at {m} {Γ : Context m} (f h k : Fin m) (hf : Derives Γ (compatible f)) :
    Derives Γ ((Formula.mem h f).imp ((Formula.mem k f).imp (agrees h k))) := by
  have hi := Derives.allE k (Derives.allE h hf)
  simpa only [Formula.instantiate, Formula.rename, agrees_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem agrees_at {m} {Γ : Context m} (f h x y z : Fin m) (hf : Derives Γ (agrees f h)) :
    Derives Γ ((edge f x y).imp ((edge h x z).imp (.equal y z))) := by
  have hi := Derives.allE z (Derives.allE y (Derives.allE x hf))
  simpa only [Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem member_edge_intro {m} {Γ : Context m} (f h x y : Fin m)
    (hm : Derives Γ (.mem h f)) (he : Derives Γ (edge h x y)) : Derives Γ (memberEdge f x y) := by
  apply Derives.exI h
  simpa only [Formula.instantiate, Formula.rename, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    using Derives.conjI hm he
end PPAC.Migration.GraphFamilySyntax
