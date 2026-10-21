import PPAC.Migration.Internal.StructuralListFieldPairs

/-! 实际完整有序字段图、全边精确式、唯一纤维与实际列表解码见证。 -/
namespace PPAC.Migration.Internal.StructuralListFieldGraphSyntax
open Source SourceAlgebra SourceLogic GraphSyntax SequenceSyntax StructuralListFieldSyntax StructuralListFieldPairSyntax StructuralListLengthSyntax

def edgeLaw {m} (w n l g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).conj (field w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def fields {m} (w n l g : Fin m) : Formula m := (sequence g l w).conj ((graph w n l g).conj (edgeLaw w n l g))

def fieldsFiber {m} (w n l : Fin m) : Formula m := .ex
  ((fields w.castSucc n.castSucc l.castSucc (Fin.last m)).conj (.all
    ((graph w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def decodedBody {m} (w n : Fin m) : Formula (m+2) :=
  ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)).conj
    (fields w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))

def decoded {m} (w n : Fin m) : Formula m := .ex (.ex (decodedBody w n))

theorem edgeLaw_rename {m k} (w n l g : Fin m) (s : Fin m → Fin k) : (edgeLaw w n l g).rename s = edgeLaw (s w) (s n) (s l) (s g) := by
  simp only [edgeLaw, Formula.rename, Formula.iff, edge_rename, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fields_rename {m k} (w n l g : Fin m) (s : Fin m → Fin k) : (fields w n l g).rename s = fields (s w) (s n) (s l) (s g) := by
  simp only [fields, Formula.rename, sequence_rename, graph_rename, edgeLaw_rename]

theorem fieldsFiber_rename {m k} (w n l : Fin m) (s : Fin m → Fin k) : (fieldsFiber w n l).rename s = fieldsFiber (s w) (s n) (s l) := by
  simp only [fieldsFiber, Formula.rename, fields_rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decoded_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (decoded w n).rename s = decoded (s w) (s n) := by
  simp only [decoded, decodedBody, Formula.rename, hasLength_rename, fields_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_at {m} {Γ : Context m} (w n l g i y : Fin m) (hg : Derives Γ (edgeLaw w n l g)) :
    Derives Γ ((edge g i y).iff ((Formula.mem i l).conj (field w n i y))) := by
  simpa only [edgeLaw, Formula.instantiate, Formula.rename, Formula.iff, edge_rename, field_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hg)

theorem graph_domain_subst {m} {Γ : Context m} (w n l k g : Fin m) (he : Derives Γ (.equal l k))
    (hg : Derives Γ (graph w n l g)) : Derives Γ (graph w n k g) := by
  have hi : Derives Γ ((graph w.castSucc n.castSucc (Fin.last m) g.castSucc).instantiate l) := by
    simpa only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hg
  have ho := Derives.eqSubst (graph w.castSucc n.castSucc (Fin.last m) g.castSucc) he hi
  simpa only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem intro_decoded {m} {Γ : Context m} (w n l g : Fin m) (hl : Derives Γ (.mem l w)) (hL : Derives Γ (hasLength w n l))
    (hg : Derives Γ (fields w n l g)) : Derives Γ (decoded w n) := by
  apply Derives.exI l
  apply Derives.exI g
  simp only [Formula.instantiate, decodedBody, Formula.rename, hasLength_rename, fields_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hl hL) hg
end PPAC.Migration.Internal.StructuralListFieldGraphSyntax
