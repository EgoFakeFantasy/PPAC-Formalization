import PPAC.Migration.Internal.SyntaxMixedImageBinderFields
import PPAC.Migration.Internal.StructuralListCodeGraph

/-! 以原自然列表码表示混合项像表；目标两类项都允许，项码不受目标变量数的数值上界限制。 -/
namespace PPAC.Migration.Internal.SyntaxMixedImageCodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax
open SyntaxTermImageSyntax (imageMap imageMap_rename)
open StructuralListEncodeSyntax (encoding encoding_rename)
open StructuralListFieldSyntax (field field_rename)
open StructuralListLengthSyntax (hasLength hasLength_rename)
open SyntaxTermSyntax (term term_rename contexts contexts_rename)

def typedFields {m} (w a c d L : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (field w.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).imp
      (term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)))))

def termList {m} (w a c d L : Fin m) : Formula m := (Formula.mem a w).conj
  ((contexts w c d).conj (((Formula.mem L w).conj (hasLength w L a)).conj (typedFields w a c d L)))

def encoded {m} (w f a c d L : Fin m) : Formula m := (imageMap w f a c d).conj (encoding w f a L)

def existsCode {m} (w f a c d : Fin m) : Formula m := .ex
  (encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m))

def existsGraph {m} (w a c d L : Fin m) : Formula m := .ex
  (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc)

def codeUnique {m} (w f a c d L : Fin m) : Formula m := .all
  ((encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).imp (.equal (Fin.last m) L.castSucc))

def graphUnique {m} (w f a c d L : Fin m) : Formula m := .all
  ((encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc).imp (.equal (Fin.last m) f.castSucc))

def codeFiber {m} (w f a c d : Fin m) : Formula m := .ex
  ((encoded w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj
    (codeUnique w.castSucc f.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)))

def graphFiber {m} (w a c d L : Fin m) : Formula m := .ex
  ((encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc).conj
    (graphUnique w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc L.castSucc))

def termLists {m} (w a b c d R S : Fin m) : Formula m := (termList w a c d R).conj (termList w b c d S)

def encodings {m} (w r s a b c d R S : Fin m) : Formula m := (encoded w r a c d R).conj (encoded w s b c d S)

theorem typedFields_rename {m k} (w a c d L : Fin m) (ρ : Fin m → Fin k) :
    (typedFields w a c d L).rename ρ = typedFields (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [typedFields, Formula.rename, field_rename, term_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem termList_rename {m k} (w a c d L : Fin m) (ρ : Fin m → Fin k) :
    (termList w a c d L).rename ρ = termList (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [termList, Formula.rename, contexts_rename, hasLength_rename, typedFields_rename]

theorem encoded_rename {m k} (w f a c d L : Fin m) (ρ : Fin m → Fin k) :
    (encoded w f a c d L).rename ρ = encoded (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [encoded, Formula.rename, imageMap_rename, encoding_rename]

theorem existsCode_rename {m k} (w f a c d : Fin m) (ρ : Fin m → Fin k) :
    (existsCode w f a c d).rename ρ = existsCode (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) := by
  simp only [existsCode, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsGraph_rename {m k} (w a c d L : Fin m) (ρ : Fin m → Fin k) :
    (existsGraph w a c d L).rename ρ = existsGraph (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [existsGraph, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeUnique_rename {m k} (w f a c d L : Fin m) (ρ : Fin m → Fin k) :
    (codeUnique w f a c d L).rename ρ = codeUnique (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [codeUnique, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphUnique_rename {m k} (w f a c d L : Fin m) (ρ : Fin m → Fin k) :
    (graphUnique w f a c d L).rename ρ = graphUnique (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [graphUnique, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeFiber_rename {m k} (w f a c d : Fin m) (ρ : Fin m → Fin k) :
    (codeFiber w f a c d).rename ρ = codeFiber (ρ w) (ρ f) (ρ a) (ρ c) (ρ d) := by
  simp only [codeFiber, Formula.rename, encoded_rename, codeUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphFiber_rename {m k} (w a c d L : Fin m) (ρ : Fin m → Fin k) :
    (graphFiber w a c d L).rename ρ = graphFiber (ρ w) (ρ a) (ρ c) (ρ d) (ρ L) := by
  simp only [graphFiber, Formula.rename, encoded_rename, graphUnique_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem termLists_rename {m k} (w a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (termLists w a b c d R S).rename ρ = termLists (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [termLists, Formula.rename, termList_rename]

theorem encodings_rename {m k} (w r s a b c d R S : Fin m) (ρ : Fin m → Fin k) :
    (encodings w r s a b c d R S).rename ρ = encodings (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ R) (ρ S) := by
  simp only [encodings, Formula.rename, encoded_rename]

theorem intro_code {m} {Γ : Context m} (w f a c d L : Fin m) (he : Derives Γ (encoded w f a c d L)) : Derives Γ (existsCode w f a c d) := by
  apply Derives.exI L
  exact of_eq (by simp only [Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem intro_graph {m} {Γ : Context m} (w f a c d L : Fin m) (he : Derives Γ (encoded w f a c d L)) : Derives Γ (existsGraph w a c d L) := by
  apply Derives.exI f
  exact of_eq (by simp only [Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem intro_code_fiber {m} {Γ : Context m} (w f a c d L : Fin m) (he : Derives Γ ((encoded w f a c d L).conj (codeUnique w f a c d L))) : Derives Γ (codeFiber w f a c d) := by
  apply Derives.exI L
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, encoded_rename, codeUnique_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

theorem intro_graph_fiber {m} {Γ : Context m} (w f a c d L : Fin m) (he : Derives Γ ((encoded w f a c d L).conj (graphUnique w f a c d L))) : Derives Γ (graphFiber w a c d L) := by
  apply Derives.exI f
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, encoded_rename, graphUnique_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he

end PPAC.Migration.Internal.SyntaxMixedImageCodeSyntax
