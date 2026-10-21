import PPAC.Migration.Internal.SyntaxAtomExistence

/-! 原子码的同输入唯一性和实际解码字段唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxAtomUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxAtomLogic
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem member_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w s x y t u v n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (memberCode w s x y n)) (hd : Derives Γ (memberCode w t u v n)) :
    Derives Γ ((Formula.equal s t).conj ((Formula.equal x u).conj (.equal y v))) := by
  have h0 := SyntaxNodeInjective.constructor_input_eq hZ 3 2 2 w (three s x y) (three t u v) n 0 hw hc hd
  have h1 := SyntaxNodeInjective.constructor_input_eq hZ 3 2 2 w (three s x y) (three t u v) n 1 hw hc hd
  have h2 := SyntaxNodeInjective.constructor_input_eq hZ 3 2 2 w (three s x y) (three t u v) n 2 hw hc hd
  exact .conjI h0 (.conjI h1 h2)

theorem equal_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x y u v n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (equalCode w x y n)) (hd : Derives Γ (equalCode w u v n)) :
    Derives Γ ((Formula.equal x u).conj (.equal y v)) := by
  have h0 := SyntaxNodeInjective.constructor_input_eq hZ 2 3 3 w (two x y) (two u v) n 0 hw hc hd
  have h1 := SyntaxNodeInjective.constructor_input_eq hZ 2 3 3 w (two x y) (two u v) n 1 hw hc hd
  exact .conjI h0 h1

theorem symbol_subst {m} {Γ : Context m} (w s t x y n : Fin m) (he : Derives Γ (.equal s t))
    (hc : Derives Γ (memberCode w s x y n)) : Derives Γ (memberCode w t x y n) := by
  have hi : Derives Γ ((memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc n.castSucc).instantiate s) := by
    simpa only [Formula.instantiate, memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc
  have ho := Derives.eqSubst (memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc n.castSucc) he hi
  simpa only [Formula.instantiate, memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem member_same_inputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f s t x y n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (memberAt w b f s x y n)) (hr : Derives Γ (memberAt w b f t x y r)) : Derives Γ (.equal n r) := by
  have heq := SyntaxZeroScalar.unique hZ w s t hw (.conjL (.conjL hn)) (.conjL (.conjL hr))
  have hc := symbol_subst w t s x y r (eq_symm heq) (.conjR hr)
  exact SyntaxConstructors.unique hZ 3 2 w (three s x y) n r hw (.conjR hn) hc

theorem equal_same_inputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f x y n r : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (equalAt w b f x y n)) (hr : Derives Γ (equalAt w b f x y r)) : Derives Γ (.equal n r) :=
  SyntaxConstructors.unique hZ 2 3 w (two x y) n r hw (.conjR hn) (.conjR hr)
end PPAC.Migration.Internal.SyntaxAtomUnique
