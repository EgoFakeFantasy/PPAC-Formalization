import PPAC.Migration.Internal.PacketReaderInputSyntax

/-! Natural actual Cons fields are unique, disjoint from Nil, and obtained from the original valid-list decomposition. -/
namespace PPAC.Migration.Internal.PacketReaderInputFields
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderInputSyntax
open StructuralListTraceSyntax (valid valid_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l b x d t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (headRest w l b x)) (hk : Derives Γ (headRest w l d t)) :
    Derives Γ ((Formula.equal b d).conj (.equal x t)) :=
  StructuralConsUnique.injective hZ w b x d t l hw (.conjL hh) (StructuralListValidity.range w x (.conjL (.conjR hh)))
    (.conjL hk) (StructuralListValidity.range w t (.conjL (.conjR hk))) (.conjR (.conjR hh)) (.conjR (.conjR hk))

theorem not_nil {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l b x : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (headRest w l b x)) : Derives Γ (StructuralListSyntax.nilCode w l).neg := by
  apply Derives.impI
  exact StructuralConsUnique.disjoint (ZFContext.add hZ _) w b x l (add hw _) (.hyp (Or.inl rfl)) (add (.conjR (.conjR hh)) _)

theorem valid_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l b x : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (headRest w l b x)) : Derives Γ (valid w l) :=
  StructuralListValidity.cons_valid hZ w b x l hw (.conjL hh) (.conjL (.conjR hh)) (.conjR (.conjR hh))

theorem rest_state {m} {Γ : Context m} (w l b x v s a : Fin m)
    (hi : Derives Γ (PacketReaderStepSyntax.state w l v s a)) (hh : Derives Γ (headRest w l b x)) :
    Derives Γ (PacketReaderStepSyntax.state w x v s a) := .conjI (.conjL (.conjR hh)) (.conjR hi)

theorem decomposition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (valid w l)) : Derives Γ ((StructuralListSyntax.nilCode w l).disj (hasHead w l)) := by
  apply Derives.disjE (StructuralListTraceInvert.valid_decomposition hZ w l hw hl)
  · exact .disjL (.hyp (Or.inl rfl))
  · let P := StructuralListDecodeSyntax.tailCase w l
    let T := (valid w.castSucc (Fin.last m)).conj (StructuralListTraceSyntax.step w.castSucc (Fin.last m) l.castSucc)
    let Δ := Context.add T (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := T) (.hyp (Or.inl rfl))
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    let H := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
      (StructuralListSyntax.consCode w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc l.castSucc.castSucc)
    let Ξ := Context.add H (Context.image Formula.raise Δ)
    apply Derives.exE (p := H) (.conjR hT)
    have hH : Derives Ξ H := .hyp (Or.inl rfl)
    have ht2 := of_eq (valid_rename w.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hT) H)
    have hhead := intro_head _ _ _ _ (.conjI (.conjL hH) (.conjI ht2 (.conjR hH)))
    have hout : Derives Ξ ((StructuralListSyntax.nilCode w.castSucc.castSucc l.castSucc.castSucc).disj (hasHead w.castSucc.castSucc l.castSucc.castSucc)) := .disjR hhead
    simpa only [Formula.raise,Formula.rename,StructuralListSyntax.nilCode_rename,hasHead_rename] using hout

end PPAC.Migration.Internal.PacketReaderInputFields
