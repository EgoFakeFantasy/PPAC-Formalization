import PPAC.Migration.Internal.ObjectStructuralTreeCheck

/-! 任意内部字段序列的原树节点构造合同；tag/长度/完整字段图均是对象参数。 -/
namespace PPAC.Migration.Internal.StructuralTreeEncodeSyntax
open Source SourceAlgebra SourceLogic GraphSyntax StructuralTreeOperatorSyntax

def encodingBody {m} (w tag l f n : Fin m) : Formula (m+1) :=
  shape w.castSucc n.castSucc tag.castSucc (Fin.last m) l.castSucc f.castSucc

def encoding {m} (w tag l f n : Fin m) : Formula m := .ex (encodingBody w tag l f n)

def existsEncoding {m} (w tag l f : Fin m) : Formula m := .ex (encoding w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m))

def uniqueAt {m} (w tag l f n : Fin m) : Formula m := .all
  ((encoding w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m)).imp (.equal (Fin.last m) n.castSucc))

def encodingFiber {m} (w tag l f : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (encoding w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m))).conj
    (uniqueAt w.castSucc tag.castSucc l.castSucc f.castSucc (Fin.last m)))

theorem encoding_rename {m k} (w tag l f n : Fin m) (s : Fin m → Fin k) : (encoding w tag l f n).rename s = encoding (s w) (s tag) (s l) (s f) (s n) := by
  simp only [encoding, encodingBody, Formula.rename, shape_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsEncoding_rename {m k} (w tag l f : Fin m) (s : Fin m → Fin k) : (existsEncoding w tag l f).rename s = existsEncoding (s w) (s tag) (s l) (s f) := by
  simp only [existsEncoding, Formula.rename, encoding_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueAt_rename {m k} (w tag l f n : Fin m) (s : Fin m → Fin k) : (uniqueAt w tag l f n).rename s = uniqueAt (s w) (s tag) (s l) (s f) (s n) := by
  simp only [uniqueAt, Formula.rename, encoding_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem encodingFiber_rename {m k} (w tag l f : Fin m) (s : Fin m → Fin k) : (encodingFiber w tag l f).rename s = encodingFiber (s w) (s tag) (s l) (s f) := by
  simp only [encodingFiber, Formula.rename, encoding_rename, uniqueAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_encoding {m} {Γ : Context m} (w tag l f n p : Fin m)
    (hs : Derives Γ (shape w n tag p l f)) : Derives Γ (encoding w tag l f n) := by
  apply Derives.exI p
  simpa only [encodingBody, Formula.instantiate, shape_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hs

theorem eliminate_encoding {m} {Γ : Context m} (w tag l f n : Fin m) (q : Formula m) (he : Derives Γ (encoding w tag l f n))
    (hc : Derives (Context.add (encodingBody w tag l f n) (Context.image Formula.raise Γ)) q.raise) : Derives Γ q := .exE he hc

theorem intro_exists {m} {Γ : Context m} (w tag l f n : Fin m) (he : Derives Γ (encoding w tag l f n)) : Derives Γ (existsEncoding w tag l f) := by
  apply Derives.exI n
  simpa only [Formula.instantiate, encoding_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using he
end PPAC.Migration.Internal.StructuralTreeEncodeSyntax
