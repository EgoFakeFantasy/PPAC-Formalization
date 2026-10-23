import PPAC.Migration.Internal.SyntaxTopEnvironmentTyping

/-! 同一首槽前缀中旧表与头项码的对象等词传输。 -/
namespace PPAC.Migration.Internal.SyntaxTopEnvironmentSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax SyntaxTermImagePrefixSyntax

theorem prefix_base {m} {Γ : Context m} (w u a c d t A f V : Fin m)
    (he : Derives Γ (.equal u V)) (hp : Derives Γ (prefixed w u a c d t A f)) :
    Derives Γ (prefixed w V a c d t A f) := by
  let P := prefixed w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc t.castSucc A.castSucc f.castSucc
  have e0 : P.instantiate u = prefixed w u a c d t A f := by
    simp only [P, Formula.instantiate, prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = prefixed w V a c d t A f := by
    simp only [P, Formula.instantiate, prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem prefix_head {m} {Γ : Context m} (w u a c d t A f V : Fin m)
    (he : Derives Γ (.equal t V)) (hp : Derives Γ (prefixed w u a c d t A f)) :
    Derives Γ (prefixed w u a c d V A f) := by
  let P := prefixed w.castSucc u.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) A.castSucc f.castSucc
  have e0 : P.instantiate t = prefixed w u a c d t A f := by
    simp only [P, Formula.instantiate, prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate V = prefixed w u a c d V A f := by
    simp only [P, Formula.instantiate, prefixed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

end PPAC.Migration.Internal.SyntaxTopEnvironmentSubst
