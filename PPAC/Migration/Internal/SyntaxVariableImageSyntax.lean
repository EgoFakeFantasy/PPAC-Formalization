import PPAC.Migration.Internal.SyntaxTermImagePrefixGraph

/-! 完整索引图到变量项码像表；值为真实bvar/fvar项码，不把索引自然数当项码。 -/
namespace PPAC.Migration.Internal.SyntaxVariableImageSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax
open SyntaxTermSyntax (term term_rename contexts contexts_rename limit limit_map)
open SyntaxIndexMapSyntax (indexMap indexMap_rename)
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open SyntaxVariableSyntax (code code_rename)

def input {m} (bound : Bool) (w r a c d : Fin m) : Formula m :=
  (contexts w c d).conj (indexMap w r a (limit bound c d))

def body {m} (bound : Bool) (w r c d i q : Fin m) : Formula (m+1) :=
  (edge r.castSucc i.castSucc (Fin.last m)).conj
    ((code bound w.castSucc (Fin.last m) q.castSucc).conj (term w.castSucc c.castSucc d.castSucc q.castSucc))

def value {m} (bound : Bool) (w r c d i q : Fin m) : Formula m := .ex (body bound w r c d i q)

def matrix {m} (bound : Bool) (w r c d : Fin m) : Formula (m+2) :=
  value bound w.castSucc.castSucc r.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def law {m} (bound : Bool) (w r a c d f : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
      (value bound w.castSucc.castSucc r.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def graph {m} (bound : Bool) (w r a c d f : Fin m) : Formula m := (functionOn f a).conj (law bound w r a c d f)

def mapped {m} (bound : Bool) (w r a c d f : Fin m) : Formula m :=
  (input bound w r a c d).conj ((imageMap w f a c d).conj (graph bound w r a c d f))

def existsMap {m} (bound : Bool) (w r a c d : Fin m) : Formula m := .ex
  (mapped bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m))

theorem input_rename {m k} (bound : Bool) (w r a c d : Fin m) (ρ : Fin m → Fin k) :
    (input bound w r a c d).rename ρ = input bound (ρ w) (ρ r) (ρ a) (ρ c) (ρ d) := by
  simp only [input, Formula.rename, contexts_rename, indexMap_rename, limit_map]

theorem value_rename {m k} (bound : Bool) (w r c d i q : Fin m) (ρ : Fin m → Fin k) :
    (value bound w r c d i q).rename ρ = value bound (ρ w) (ρ r) (ρ c) (ρ d) (ρ i) (ρ q) := by
  simp only [value, body, Formula.rename, edge_rename, code_rename, term_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rel {p m} (bound : Bool) (w r c d : Fin p) (ρ : Fin p → Fin m) (i q : Fin m) :
    rel (matrix bound w r c d) ρ i q = value bound (ρ w) (ρ r) (ρ c) (ρ d) i q := by
  simp only [rel, Source.SetLanguage.relation, matrix, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_rename {m k} (bound : Bool) (w r a c d f : Fin m) (ρ : Fin m → Fin k) :
    (law bound w r a c d f).rename ρ = law bound (ρ w) (ρ r) (ρ a) (ρ c) (ρ d) (ρ f) := by
  simp only [law, Formula.iff, Formula.rename, edge_rename, value_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graph_rename {m k} (bound : Bool) (w r a c d f : Fin m) (ρ : Fin m → Fin k) :
    (graph bound w r a c d f).rename ρ = graph bound (ρ w) (ρ r) (ρ a) (ρ c) (ρ d) (ρ f) := by
  simp only [graph, Formula.rename, functionOn_rename, law_rename]

theorem mapped_rename {m k} (bound : Bool) (w r a c d f : Fin m) (ρ : Fin m → Fin k) :
    (mapped bound w r a c d f).rename ρ = mapped bound (ρ w) (ρ r) (ρ a) (ρ c) (ρ d) (ρ f) := by
  simp only [mapped, Formula.rename, input_rename, imageMap_rename, graph_rename]

theorem existsMap_rename {m k} (bound : Bool) (w r a c d : Fin m) (ρ : Fin m → Fin k) :
    (existsMap bound w r a c d).rename ρ = existsMap bound (ρ w) (ρ r) (ρ a) (ρ c) (ρ d) := by
  simp only [existsMap, Formula.rename, mapped_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_graph {p m} (bound : Bool) (w r c d : Fin p) (ρ : Fin p → Fin m) (a f : Fin m) :
    RelationGraphSyntax.functionGraph (matrix bound w r c d) ρ a f = graph bound (ρ w) (ρ r) a (ρ c) (ρ d) f := by
  simp only [RelationGraphSyntax.functionGraph, RelationGraphSyntax.edgeLaw, matrix_rel, paramsUp, graph, law]

theorem intro_value {m} {Γ : Context m} (bound : Bool) (w r c d i q j : Fin m)
    (he : Derives Γ (edge r i j)) (hc : Derives Γ (code bound w j q)) (ht : Derives Γ (term w c d q)) :
    Derives Γ (value bound w r c d i q) := by
  apply Derives.exI j
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, edge_rename, code_rename, term_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he (.conjI hc ht))

theorem intro_exists {m} {Γ : Context m} (bound : Bool) (w r a c d f : Fin m)
    (hh : Derives Γ (mapped bound w r a c d f)) : Derives Γ (existsMap bound w r a c d) := by
  apply Derives.exI f
  exact of_eq (by simp only [Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
end PPAC.Migration.Internal.SyntaxVariableImageSyntax
