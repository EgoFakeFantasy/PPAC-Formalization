import PPAC.Migration.Internal.SyntaxTermImageBoundShift
import PPAC.Migration.Internal.SyntaxIndexLiftOrder

/-! 混合binder提升的源bound头槽扩展：新0取指定项码，旧i移到Succ(i)，项码值不做数值后继。 -/
namespace PPAC.Migration.Internal.SyntaxTermImagePrefixSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)

def shiftedBody {m} (f a i q : Fin m) : Formula (m+1) :=
  (Formula.mem (Fin.last m) a.castSucc).conj
    ((successor i.castSucc (Fin.last m)).conj (edge f.castSucc (Fin.last m) q.castSucc))

def shifted {m} (f a i q : Fin m) : Formula m := .ex (shiftedBody f a i q)

def value {m} (f a z i q : Fin m) : Formula m :=
  ((empty i).conj (Formula.equal q z)).disj (shifted f a i q)

def matrix {m} (f a z : Fin m) : Formula (m+2) :=
  value f.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def law {m} (f a z A g : Fin m) : Formula m := .all (.all
  ((edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc A.castSucc.castSucc).conj
      (value f.castSucc.castSucc a.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def graph {m} (f a z A g : Fin m) : Formula m := (functionOn g A).conj (law f a z A g)

def prefixed {m} (w f a c d z A g : Fin m) : Formula m := (imageMap w f a c d).conj
  ((SyntaxTermSyntax.term w c d z).conj ((successor A a).conj
    ((imageMap w g A c d).conj (graph f a z A g))))

def existsPrefix {m} (w f a c d z A : Fin m) : Formula m := .ex
  (prefixed w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc z.castSucc A.castSucc (Fin.last m))

theorem shifted_rename {m k} (f a i q : Fin m) (ρ : Fin m → Fin k) :
    (shifted f a i q).rename ρ = shifted (ρ f) (ρ a) (ρ i) (ρ q) := by
  simp only [shifted, shiftedBody, Formula.rename, successor_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (f a z i q : Fin m) (ρ : Fin m → Fin k) :
    (value f a z i q).rename ρ = value (ρ f) (ρ a) (ρ z) (ρ i) (ρ q) := by
  simp only [value, Formula.rename, empty_rename, shifted_rename]

theorem matrix_rel {p m} (f a z : Fin p) (ρ : Fin p → Fin m) (i q : Fin m) :
    rel (matrix f a z) ρ i q = value (ρ f) (ρ a) (ρ z) i q := by
  simp only [rel, Source.SetLanguage.relation, matrix, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem law_rename {m k} (f a z A g : Fin m) (ρ : Fin m → Fin k) :
    (law f a z A g).rename ρ = law (ρ f) (ρ a) (ρ z) (ρ A) (ρ g) := by
  simp only [law, Formula.iff, Formula.rename, edge_rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graph_rename {m k} (f a z A g : Fin m) (ρ : Fin m → Fin k) :
    (graph f a z A g).rename ρ = graph (ρ f) (ρ a) (ρ z) (ρ A) (ρ g) := by
  simp only [graph, Formula.rename, functionOn_rename, law_rename]

theorem prefixed_rename {m k} (w f a c d z A g : Fin m) (ρ : Fin m → Fin k) :
    (prefixed w f a c d z A g).rename ρ = prefixed (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) (ρ z) (ρ A) (ρ g) := by
  simp only [prefixed, Formula.rename, imageMap_rename, SyntaxTermSyntax.term_rename, successor_rename, graph_rename]

theorem existsPrefix_rename {m k} (w f a c d z A : Fin m) (ρ : Fin m → Fin k) :
    (existsPrefix w f a c d z A).rename ρ = existsPrefix (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) (ρ z) (ρ A) := by
  simp only [existsPrefix, Formula.rename, prefixed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_graph {p m} (f a z : Fin p) (ρ : Fin p → Fin m) (A g : Fin m) :
    RelationGraphSyntax.functionGraph (matrix f a z) ρ A g = graph (ρ f) (ρ a) (ρ z) A g := by
  simp only [RelationGraphSyntax.functionGraph, RelationGraphSyntax.edgeLaw, matrix_rel, paramsUp, graph, law]

theorem intro_shifted {m} {Γ : Context m} (f a i q k : Fin m) (hk : Derives Γ (.mem k a))
    (hi : Derives Γ (successor i k)) (he : Derives Γ (edge f k q)) : Derives Γ (shifted f a i q) := by
  apply Derives.exI k
  exact of_eq (by simp only [shiftedBody, Formula.instantiate, Formula.rename, successor_rename, edge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hk (.conjI hi he))

theorem intro_exists {m} {Γ : Context m} (w f a c d z A g : Fin m)
    (hg : Derives Γ (prefixed w f a c d z A g)) : Derives Γ (existsPrefix w f a c d z A) := by
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hg

end PPAC.Migration.Internal.SyntaxTermImagePrefixSyntax
