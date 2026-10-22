import PPAC.Migration.Internal.SyntaxTermImageGraph

/-! 对实际完整项像表的每个值施加同一目标重命名；不按源bound/free类别省略变换。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePushSyntax
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates
open SyntaxRenameTermSyntax (renamed renamed_rename)
open SyntaxTermImageSyntax (imageMap imageMap_rename)

def value {m} (w R S c d C D f i q : Fin m) : Formula m := .ex
  ((edge f.castSucc i.castSucc (Fin.last m)).conj
    (renamed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc (Fin.last m) q.castSucc))

def matrix {m} (w R S c d C D f : Fin m) : Formula (m+2) :=
  value w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
    C.castSucc.castSucc D.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def law {m} (w R S c d C D f a g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
      (value w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
        C.castSucc.castSucc D.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def graph {m} (w R S c d C D f a g : Fin m) : Formula m := (functionOn g a).conj (law w R S c d C D f a g)

def pushed {m} (w R S c d C D f a g : Fin m) : Formula m := (imageMap w f a c d).conj
  ((SyntaxIndexMapSyntax.maps w R S c d C D).conj ((imageMap w g a C D).conj (graph w R S c d C D f a g)))

def existsPush {m} (w R S c d C D f a : Fin m) : Formula m := .ex
  (pushed w.castSucc R.castSucc S.castSucc c.castSucc d.castSucc C.castSucc D.castSucc f.castSucc a.castSucc (Fin.last m))

theorem value_rename {m k} (w R S c d C D f i q : Fin m) (ρ : Fin m → Fin k) :
    (value w R S c d C D f i q).rename ρ = value (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) (ρ i) (ρ q) := by
  simp only [value, Formula.rename, edge_rename, renamed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {p m} (w R S c d C D f : Fin p) (ρ : Fin p → Fin m) (i q : Fin m) :
    rel (matrix w R S c d C D f) ρ i q = value (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) i q := by
  simp only [rel, Source.SetLanguage.relation, matrix, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_rename {m k} (w R S c d C D f a g : Fin m) (ρ : Fin m → Fin k) :
    (law w R S c d C D f a g).rename ρ = law (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) (ρ a) (ρ g) := by
  simp only [law, Formula.iff, Formula.rename, edge_rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graph_rename {m k} (w R S c d C D f a g : Fin m) (ρ : Fin m → Fin k) :
    (graph w R S c d C D f a g).rename ρ = graph (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) (ρ a) (ρ g) := by
  simp only [graph, Formula.rename, functionOn_rename, law_rename]

theorem pushed_rename {m k} (w R S c d C D f a g : Fin m) (ρ : Fin m → Fin k) :
    (pushed w R S c d C D f a g).rename ρ = pushed (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) (ρ a) (ρ g) := by
  simp only [pushed, Formula.rename, imageMap_rename, SyntaxIndexMapSyntax.maps_rename, graph_rename]

theorem existsPush_rename {m k} (w R S c d C D f a : Fin m) (ρ : Fin m → Fin k) :
    (existsPush w R S c d C D f a).rename ρ = existsPush (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) (ρ a) := by
  simp only [existsPush, Formula.rename, pushed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_graph {p m} (w R S c d C D f : Fin p) (ρ : Fin p → Fin m) (a g : Fin m) :
    RelationGraphSyntax.functionGraph (matrix w R S c d C D f) ρ a g = graph (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ C) (ρ D) (ρ f) a g := by
  simp only [RelationGraphSyntax.functionGraph, RelationGraphSyntax.edgeLaw, matrix_rel, paramsUp, graph, law]

theorem intro_value {m} {Γ : Context m} (w R S c d C D f i q t : Fin m)
    (he : Derives Γ (edge f i t)) (hq : Derives Γ (renamed w R S c d C D t q)) : Derives Γ (value w R S c d C D f i q) := by
  apply Derives.exI t
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, renamed_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hq)

theorem intro_exists {m} {Γ : Context m} (w R S c d C D f a g : Fin m)
    (hg : Derives Γ (pushed w R S c d C D f a g)) : Derives Γ (existsPush w R S c d C D f a) := by
  apply Derives.exI g
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, pushed_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hg

end PPAC.Migration.Internal.SyntaxTermImagePushSyntax
