import PPAC.Migration.Internal.ObjectSyntaxIndexLift

/-! 完整有限索引图的原自然列表码；保留实际图、原长度与目标范围。 -/
namespace PPAC.Migration.Internal.SyntaxMapCodeSyntax
open Source SourceAlgebra SourceLogic StructuralListEncodeSyntax SyntaxIndexMapSyntax

def encoded {m} (w r a c k : Fin m) : Formula m := (encoding w r a k).conj (indexMap w r a c)

def mapCode {m} (w a c k : Fin m) : Formula m := .ex
  (encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc)

def existsCode {m} (w r a c : Fin m) : Formula m := .ex
  (encoded w.castSucc r.castSucc a.castSucc c.castSucc (Fin.last m))

def codeFiber {m} (w r a c : Fin m) : Formula m := .ex
  ((encoded w.castSucc r.castSucc a.castSucc c.castSucc (Fin.last m)).conj
    (.all ((encoded w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def graphFiber {m} (w a c k : Fin m) : Formula m := .ex
  ((encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc).conj
    (.all ((encoded w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc k.castSucc.castSucc).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem encoded_rename {m n} (w r a c k : Fin m) (ρ : Fin m → Fin n) :
    (encoded w r a c k).rename ρ = encoded (ρ w) (ρ r) (ρ a) (ρ c) (ρ k) := by
  simp only [encoded, Formula.rename, encoding_rename, indexMap_rename]

theorem mapCode_rename {m n} (w a c k : Fin m) (ρ : Fin m → Fin n) :
    (mapCode w a c k).rename ρ = mapCode (ρ w) (ρ a) (ρ c) (ρ k) := by
  simp only [mapCode, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsCode_rename {m n} (w r a c : Fin m) (ρ : Fin m → Fin n) :
    (existsCode w r a c).rename ρ = existsCode (ρ w) (ρ r) (ρ a) (ρ c) := by
  simp only [existsCode, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem codeFiber_rename {m n} (w r a c : Fin m) (ρ : Fin m → Fin n) :
    (codeFiber w r a c).rename ρ = codeFiber (ρ w) (ρ r) (ρ a) (ρ c) := by
  simp only [codeFiber, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem graphFiber_rename {m n} (w a c k : Fin m) (ρ : Fin m → Fin n) :
    (graphFiber w a c k).rename ρ = graphFiber (ρ w) (ρ a) (ρ c) (ρ k) := by
  simp only [graphFiber, Formula.rename, encoded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_code {m} {Γ : Context m} (w r a c k : Fin m) (he : Derives Γ (encoded w r a c k)) :
    Derives Γ (mapCode w a c k) := by
  apply Derives.exI r
  simpa only [Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using he

theorem graph_subst {m} {Γ : Context m} (w r s a c k : Fin m)
    (he : Derives Γ (.equal r s)) (hr : Derives Γ (encoded w r a c k)) : Derives Γ (encoded w s a c k) := by
  let P := encoded w.castSucc (Fin.last m) a.castSucc c.castSucc k.castSucc
  have hi : Derives Γ (P.instantiate r) := by simpa only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hr
  have ho := Derives.eqSubst P he hi
  simpa only [P, Formula.instantiate, encoded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxMapCodeSyntax
