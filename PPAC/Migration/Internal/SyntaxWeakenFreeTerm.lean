import PPAC.Migration.Internal.SyntaxIdentityUnique
import PPAC.Migration.Internal.SyntaxFreeShiftCode

/-! 实际恒等/位移码下，原内部项的 bound 索引保持、free 索引后继精确律。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeTerm
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeShiftSyntax (shiftCode)
open SyntaxMapCodeSyntax (encoded)
open SyntaxRenameTermSyntax (renamed)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem repeat_guard_iff {m} {Γ : Context m} (P Q E : Formula m)
    (he : Derives Γ (E.iff (P.conj Q))) : Derives Γ ((P.conj E).iff (P.conj Q)) := by
  apply Derives.conjI
  · apply Derives.impI
    have hh : Derives (Context.add (P.conj E) Γ) (P.conj E) := .hyp (Or.inl rfl)
    exact .impE (.conjL (add he _)) (.conjR hh)
  · apply Derives.impI
    have hh : Derives (Context.add (P.conj Q) Γ) (P.conj Q) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hh) (.impE (.conjR (add he _)) hh)

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hn : Derives Γ (SyntaxVariableSyntax.code true w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code true w j q)) :
    Derives Γ ((renamed w r s a b a B n q).iff ((Formula.mem i a).conj (.equal i j))) := by
  have h0 : Derives Γ ((renamed w r s a b a B n q).iff ((Formula.mem i a).conj (GraphSyntax.edge r i j))) := by
    simpa [SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap] using
      SyntaxRenameTermKnown.known_iff hZ true w r s a b a B n q i j hw (.conjI (.conjR hr) (.conjR hs)) hn hq
  have hd := SyntaxIdentityCode.at_graph hZ w a R r hR hr
  have he := SyntaxIdentityUnique.edge_iff hZ w a r i j (.conjR hr) hd
  exact SyntaxTypeLocalTransfer.iff_trans h0 (repeat_guard_iff _ _ _ he)

theorem free_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hn : Derives Γ (SyntaxVariableSyntax.code false w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code false w j q)) :
    Derives Γ ((renamed w r s a b a B n q).iff ((Formula.mem i b).conj (successor j i))) := by
  have h0 : Derives Γ ((renamed w r s a b a B n q).iff ((Formula.mem i b).conj (GraphSyntax.edge s i j))) := by
    simpa [SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap] using
      SyntaxRenameTermKnown.known_iff hZ false w r s a b a B n q i j hw (.conjI (.conjR hr) (.conjR hs)) hn hq
  have hm := SyntaxFreeShiftCode.at_graph hZ w b B S s hS hs
  have he := SyntaxFreeShiftGraph.edge_iff b s i j (SyntaxFreeShiftGraph.to_graph w b B s hm)
  exact SyntaxTypeLocalTransfer.iff_trans h0 (repeat_guard_iff _ _ _ he)

theorem fresh_free_absent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hn : Derives Γ (SyntaxVariableSyntax.code false w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code false w j q))
    (hj : Derives Γ (empty j)) : Derives Γ (renamed w r s a b a B n q).neg := by
  have he := free_iff hZ w a b B R S r s n q i j hw hS hr hs hn hq
  apply Derives.impI
  have hR : Derives (Context.add (renamed w r s a b a B n q) Γ) (renamed w r s a b a B n q) := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (add he _)) hR
  exact .impE (empty_at j i (add hj _)) (InsertLogic.new_member j i i (.conjR hi))

theorem empty_free_absent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hn : Derives Γ (SyntaxVariableSyntax.code false w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code false w j q))
    (hb : Derives Γ (empty b)) : Derives Γ (renamed w r s a b a B n q).neg := by
  have he := free_iff hZ w a b B R S r s n q i j hw hS hr hs hn hq
  apply Derives.impI
  have hR : Derives (Context.add (renamed w r s a b a B n q) Γ) (renamed w r s a b a B n q) := .hyp (Or.inl rfl)
  have hi := Derives.impE (.conjL (add he _)) hR
  exact .impE (empty_at b i (add hb _)) (.conjL hi)
end PPAC.Migration.Internal.SyntaxWeakenFreeTerm
