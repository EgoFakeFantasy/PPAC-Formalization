import PPAC.Migration.Internal.PacketBytesExecutionDomain

/-! Both actual Cons branches use proved field naturality, original injectivity and the smaller joint uniqueness clause. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionUniqueValues
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b h x u d y v : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x n)) (hd : Derives Γ (StructuralListSyntax.consCode w d y n))
    (hx : Derives Γ (bytes w x t u)) (hy : Derives Γ (bytes w y t v))
    (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) (hb : Derives Γ (PacketAffineAcceptedSyntax.accepted true w d v b)) : Derives Γ (.equal a b) := by
  have hdata := PacketBytesExecutionAffine.data hZ w h u a hw ha
  have ddata := PacketBytesExecutionAffine.data hZ w d v b hw hb
  have hhW := PacketByteInputLaws.byte_natural hZ w h hw (.conjL hdata)
  have hdW := PacketByteInputLaws.byte_natural hZ w d hw (.conjL ddata)
  have hxW := PacketBytesExecutionAffine.bytes_input_natural w x t u hx
  have hyW := PacketBytesExecutionAffine.bytes_input_natural w y t v hy
  have hp := StructuralConsUnique.injective hZ w h x d y n hw hhW hxW hdW hyW hc hd
  have hyx := PacketBytesExecutionTransport.input_subst w y t v x (eq_symm (.conjR hp)) hy
  have hxP := PacketBytesExecutionDescent.accepted_tail_property hZ w n t a h x u hw hi hc hx ha
  have huv := unique_at w x t u v hxP hx hyx
  have had := PacketBytesExecutionTransport.affine_digit w h u a d (.conjL hp) ha
  have hav := PacketBytesExecutionTransport.affine_tail w d u a v huv had
  exact PacketBytesExecutionAffine.unique_cell hZ w d v a b hw hav hb

theorem nil_cons_false {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (hc : Derives Γ (PacketBytesRecursionSyntax.actualCons w n t a)) : Derives Γ .bot := by
  let R := PacketBytesRecursionSyntax.actualBody w n t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hn3 := of_eq (StructuralListSyntax.nilCode_rename w n (old 3)) (HornBinderRules.under_body 3 hn R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact StructuralConsUnique.disjoint hZ3 (old 3 w) (slot 3 0) (slot 3 1) (old 3 n) hw3 hn3 (.conjL hR)

theorem cases_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n))
    (ha : Derives Γ (PacketBytesRecursionSyntax.actualCons w n t a)) (hb : Derives Γ (PacketBytesRecursionSyntax.actualCons w n t b)) :
    Derives Γ (.equal a b) := by
  let R := PacketBytesRecursionSyntax.actualBody w n t a
  let ΓR := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ ha
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hi3 := of_eq (earlier_rename w n (old 3)) (HornBinderRules.under_body 3 hi R)
  have hb3 := of_eq (PacketBytesRecursionSyntax.actualCons_rename w n t b (old 3)) (HornBinderRules.under_body 3 hb R)
  let S := PacketBytesRecursionSyntax.actualBody (old 3 w) (old 3 n) (old 3 t) (old 3 b)
  let Δ := Context.add S (raisedContext 3 ΓR)
  apply HornBinderRules.eliminate_many 3 S _ hb3
  have hZ6 := HornBinderRules.zf_body 3 hZ3 S
  have hw6 := of_eq (omega_rename (old 3 w) (old 3)) (HornBinderRules.under_body 3 hw3 S)
  have hi6 := of_eq (earlier_rename (old 3 w) (old 3 n) (old 3)) (HornBinderRules.under_body 3 hi3 S)
  have hR : Derives ΓR R := .hyp (Or.inl rfl)
  have hc0 := of_eq (StructuralListSyntax.consCode_rename (old 3 w) (slot 3 0) (slot 3 1) (old 3 n) (old 3)) (HornBinderRules.under_body 3 (.conjL hR) S)
  have hx0 := of_eq (bytes_rename (old 3 w) (slot 3 1) (old 3 t) (slot 3 2) (old 3)) (HornBinderRules.under_body 3 (.conjL (.conjR hR)) S)
  have ha0 := of_eq (PacketAffineAcceptedSyntax.accepted_rename true (old 3 w) (slot 3 0) (slot 3 2) (old 3 a) (old 3)) (HornBinderRules.under_body 3 (.conjR (.conjR hR)) S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  exact values hZ6 (old 3 (old 3 w)) (old 3 (old 3 n)) (old 3 (old 3 t)) (old 3 (old 3 a)) (old 3 (old 3 b))
    (old 3 (slot 3 0)) (old 3 (slot 3 1)) (old 3 (slot 3 2)) (slot 3 0) (slot 3 1) (slot 3 2) hw6 hi6 hc0 (.conjL hS)
    hx0 (.conjL (.conjR hS)) ha0 (.conjR (.conjR hS))

end PPAC.Migration.Internal.PacketBytesExecutionUniqueValues
