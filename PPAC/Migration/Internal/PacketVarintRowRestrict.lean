import PPAC.Migration.Internal.PacketVarintPrefixConstruct

/-! Both restricted sequences preserve every actual old varint row, including its complete witness block. -/
namespace PPAC.Migration.Internal.PacketVarintRowRestrict
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketVarintRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem row_restrict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C p l f g F G i : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (hF : Derives Γ (RestrictionSyntax.restrict F f l)) (hG : Derives Γ (RestrictionSyntax.restrict G g l))
    (hi : Derives Γ (.mem i p)) (hr : Derives Γ (row w C f g i)) : Derives Γ (row w C F G i) := by
  have hiW := StructuralListTraceOrder.member_member hZ w i p hw hp hi
  let R := rowBody w C f g i
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hr
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw R)
  have hs6 := of_eq (successor_rename l p (old 6)) (HornBinderRules.under_body 6 hs R)
  have hF6 := of_eq (RestrictionSyntax.restrict_rename F f l (old 6)) (HornBinderRules.under_body 6 hF R)
  have hG6 := of_eq (RestrictionSyntax.restrict_rename G g l (old 6)) (HornBinderRules.under_body 6 hG R)
  have hp6 : Derives Δ (.mem (old 6 p) (old 6 w)) := HornBinderRules.under_body 6 hp R
  have hi6 : Derives Δ (.mem (old 6 i) (old 6 p)) := HornBinderRules.under_body 6 hi R
  have hiW6 : Derives Δ (.mem (old 6 i) (old 6 w)) := HornBinderRules.under_body 6 hiW R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hil := InsertLogic.old_member _ _ _ _ hs6 hi6
  have hjp := GodelPairArithmetic.successor_below hZ6 _ _ _ _ hw6 hiW6 hp6 (.conjL hR) hi6
  have hjl := NaturalOrderBasic.below_successor _ _ _ hs6 hjp
  have hx := RestrictionEdges.restricted_edge _ _ _ _ _ hF6 (.conjL (.conjR hR)) hil
  have hy := RestrictionEdges.restricted_edge _ _ _ _ _ hF6 (.conjL (.conjR (.conjR hR))) hjl
  have hu := RestrictionEdges.restricted_edge _ _ _ _ _ hG6 (.conjL (.conjR (.conjR (.conjR (.conjR hR))))) hil
  have hv := RestrictionEdges.restricted_edge _ _ _ _ _ hG6 (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR)))))) hjl
  exact of_eq (row_rename w C F G i (old 6)).symm
    (intro_row (old 6 w) (old 6 C) (old 6 F) (old 6 G) (old 6 i)
      (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)
      (.conjL hR) hx hy (.conjL (.conjR (.conjR (.conjR hR)))) hu hv
      (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR)))))))

theorem links_restrict {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C p l f g F G : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (hl : Derives Γ (links w C l f g)) (hF : Derives Γ (RestrictionSyntax.restrict F f l))
    (hG : Derives Γ (RestrictionSyntax.restrict G g l)) : Derives Γ (links w C p F G) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) p.castSucc
  have hZ1 := ZFContext.under hZ M
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw M)
  have hs1 := of_eq (successor_rename l p Fin.castSucc) (under hs M)
  have hl1 := of_eq (links_rename w C l f g Fin.castSucc) (under hl M)
  have hF1 := of_eq (RestrictionSyntax.restrict_rename F f l Fin.castSucc) (under hF M)
  have hG1 := of_eq (RestrictionSyntax.restrict_rename G g l Fin.castSucc) (under hG M)
  have hi : Derives (Context.add M (Context.image Formula.raise Γ)) M := .hyp (Or.inl rfl)
  have hil := InsertLogic.old_member _ _ _ _ hs1 hi
  exact row_restrict hZ1 _ _ _ _ _ _ _ _ _ hw1 (under hp M) hs1 hF1 hG1 hi (links_at _ _ _ _ _ _ hl1 hil)

end PPAC.Migration.Internal.PacketVarintRowRestrict
