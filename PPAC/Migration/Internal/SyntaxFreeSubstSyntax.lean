import PPAC.Migration.Internal.SyntaxOpenTerm
import PPAC.Migration.Internal.SyntaxWeakenFreeUnique

/-! 原 free 替换参数保留项码列表；实际项字段图和实际索引图由纯对象关系连接。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstSyntax
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax
open SyntaxVariableSyntax (code code_rename)
open SyntaxTermSyntax (contexts contexts_rename branch branch_rename)
open StructuralListEncodeSyntax (encoding encoding_rename)
open SyntaxIndexMapSyntax (indexMap indexMap_rename)

def values {m} (w f c : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (branch false w.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)))))

def termGraph {m} (w f a c : Fin m) : Formula m := (contexts w a c).conj
  ((SequenceSyntax.sequence f a w).conj (values w f c))

def decodedValue {m} (w f i j : Fin m) : Formula m := .ex
  ((edge f.castSucc i.castSucc (Fin.last m)).conj
    (code false w.castSucc j.castSucc (Fin.last m)))

def encodedValue {m} (w r i t : Fin m) : Formula m := .ex
  ((edge r.castSucc i.castSucc (Fin.last m)).conj
    (code false w.castSucc (Fin.last m) t.castSucc))

def decodeMatrix : Formula 4 := decodedValue (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)

def encodeMatrix : Formula 4 := encodedValue (0 : Fin 2).castSucc.castSucc (1 : Fin 2).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)

def decodedGraph {m} (w f a r : Fin m) : Formula m :=
  RelationGraphSyntax.functionGraph decodeMatrix (Source.SetLanguage.args2 w f) a r

def encodedGraph {m} (w r a f : Fin m) : Formula m :=
  RelationGraphSyntax.functionGraph encodeMatrix (Source.SetLanguage.args2 w r) a f

def conversion {m} (w f a c r : Fin m) : Formula m :=
  (termGraph w f a c).conj ((indexMap w r a c).conj (decodedGraph w f a r))

def listBody {m} (w a c L : Fin m) : Formula (m+1) :=
  (encoding w.castSucc (Fin.last m) a.castSucc L.castSucc).conj
    (termGraph w.castSucc (Fin.last m) a.castSucc c.castSucc)

def termList {m} (w a c L : Fin m) : Formula m := .ex (listBody w a c L)

def codeBody {m} (w a c L S : Fin m) : Formula (m+2) :=
  (encoding w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc L.castSucc.castSucc).conj
    ((conversion w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))).conj
      (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc S.castSucc.castSucc))

def codeConversion {m} (w a c L S : Fin m) : Formula m := .ex (.ex (codeBody w a c L S))

theorem values_rename {m k} (w f c : Fin m) (ρ : Fin m → Fin k) :
    (values w f c).rename ρ = values (ρ w) (ρ f) (ρ c) := by
  simp only [values, Formula.rename, edge_rename, branch_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem termGraph_rename {m k} (w f a c : Fin m) (ρ : Fin m → Fin k) :
    (termGraph w f a c).rename ρ = termGraph (ρ w) (ρ f) (ρ a) (ρ c) := by
  simp only [termGraph, Formula.rename, contexts_rename, SequenceSyntax.sequence_rename, values_rename]

theorem decodedValue_rename {m k} (w f i j : Fin m) (ρ : Fin m → Fin k) :
    (decodedValue w f i j).rename ρ = decodedValue (ρ w) (ρ f) (ρ i) (ρ j) := by
  simp only [decodedValue, Formula.rename, edge_rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem encodedValue_rename {m k} (w r i t : Fin m) (ρ : Fin m → Fin k) :
    (encodedValue w r i t).rename ρ = encodedValue (ρ w) (ρ r) (ρ i) (ρ t) := by
  simp only [encodedValue, Formula.rename, edge_rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decodeMatrix_rel {m} (ρ : Fin 2 → Fin m) (i j : Fin m) :
    rel decodeMatrix ρ i j = decodedValue (ρ 0) (ρ 1) i j := by
  simp only [rel, Source.SetLanguage.relation, decodeMatrix, decodedValue_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem encodeMatrix_rel {m} (ρ : Fin 2 → Fin m) (i t : Fin m) :
    rel encodeMatrix ρ i t = encodedValue (ρ 0) (ρ 1) i t := by
  simp only [rel, Source.SetLanguage.relation, encodeMatrix, encodedValue_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem decodedGraph_rename {m k} (w f a r : Fin m) (ρ : Fin m → Fin k) :
    (decodedGraph w f a r).rename ρ = decodedGraph (ρ w) (ρ f) (ρ a) (ρ r) := by
  simp only [decodedGraph, RelationGraphSyntax.functionGraph_rename]
  rfl

theorem encodedGraph_rename {m k} (w r a f : Fin m) (ρ : Fin m → Fin k) :
    (encodedGraph w r a f).rename ρ = encodedGraph (ρ w) (ρ r) (ρ a) (ρ f) := by
  simp only [encodedGraph, RelationGraphSyntax.functionGraph_rename]
  rfl

theorem conversion_rename {m k} (w f a c r : Fin m) (ρ : Fin m → Fin k) :
    (conversion w f a c r).rename ρ = conversion (ρ w) (ρ f) (ρ a) (ρ c) (ρ r) := by
  simp only [conversion, Formula.rename, termGraph_rename, indexMap_rename, decodedGraph_rename]

theorem termList_rename {m k} (w a c L : Fin m) (ρ : Fin m → Fin k) :
    (termList w a c L).rename ρ = termList (ρ w) (ρ a) (ρ c) (ρ L) := by
  simp only [termList, listBody, Formula.rename, encoding_rename, termGraph_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeConversion_rename {m k} (w a c L S : Fin m) (ρ : Fin m → Fin k) :
    (codeConversion w a c L S).rename ρ = codeConversion (ρ w) (ρ a) (ρ c) (ρ L) (ρ S) := by
  simp only [codeConversion, codeBody, Formula.rename, encoding_rename, conversion_rename, SyntaxMapCodeSyntax.encoded_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem values_at {m} {Γ : Context m} (w f c i t : Fin m) (hv : Derives Γ (values w f c)) :
    Derives Γ ((edge f i t).imp (branch false w c t)) :=
  of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, branch_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t (Derives.allE i hv))

theorem intro_decoded {m} {Γ : Context m} (w f i j t : Fin m)
    (he : Derives Γ (edge f i t)) (hc : Derives Γ (code false w j t)) : Derives Γ (decodedValue w f i j) := by
  apply Derives.exI t
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, code_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hc)

theorem intro_encoded {m} {Γ : Context m} (w r i t j : Fin m)
    (he : Derives Γ (edge r i j)) (hc : Derives Γ (code false w j t)) : Derives Γ (encodedValue w r i t) := by
  apply Derives.exI j
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, edge_rename, code_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI he hc)

theorem intro_list {m} {Γ : Context m} (w a c L f : Fin m)
    (hL : Derives Γ (encoding w f a L)) (hf : Derives Γ (termGraph w f a c)) : Derives Γ (termList w a c L) := by
  apply Derives.exI f
  exact of_eq (by simp only [listBody, Formula.instantiate, Formula.rename, encoding_rename, termGraph_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hL hf)

theorem intro_code_conversion {m} {Γ : Context m} (w a c L S f r : Fin m)
    (hL : Derives Γ (encoding w f a L)) (hf : Derives Γ (conversion w f a c r))
    (hS : Derives Γ (SyntaxMapCodeSyntax.encoded w r a c S)) : Derives Γ (codeConversion w a c L S) := by
  apply Derives.exI f
  apply Derives.exI r
  exact of_eq (by simp only [codeBody, Formula.instantiate, Formula.rename, encoding_rename, conversion_rename,
    SyntaxMapCodeSyntax.encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI hL (.conjI hf hS))

theorem eliminate_code_conversion {m} {Γ : Context m} (w a c L S : Fin m) (P : Formula m)
    (he : Derives Γ (codeConversion w a c L S))
    (hc : Derives (Context.add (codeBody w a c L S) (Context.image Formula.raise (Context.image Formula.raise Γ))) P.raise.raise) :
    Derives Γ P := SyntaxRenameBinders.eliminate_2 (codeBody w a c L S) P he hc

end PPAC.Migration.Internal.SyntaxFreeSubstSyntax
