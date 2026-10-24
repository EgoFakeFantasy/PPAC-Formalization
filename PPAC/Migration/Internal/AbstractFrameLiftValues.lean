import PPAC.Migration.Internal.AbstractFrameLiftPoint
import PPAC.Migration.Internal.StructuralListFieldValues

/-! 实际旧变量码和旧列表字段值在对象EX中取得并消去，不作为提升端点的额外假设。 -/
namespace PPAC.Migration.Internal.AbstractFrameLiftValues
open Source SourceAlgebra SourceLogic OmegaSyntax AbstractOperationFrameSyntax AbstractVariableValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bound_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n i j X q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i A)) (hj : Derives Γ (.mem j a)) (hij : Derives Γ (successor i j))
    (hX : Derives Γ (SyntaxVariableSyntax.code true w i X)) :
    Derives Γ ((boundValue w D i X q).iff (StructuralListFieldSyntax.field w K i q)) := by
  have ha := Derives.conjL (Derives.conjL (term_lists w mode depth P a b c e R S hF))
  have hjn := StructuralListTraceOrder.member_member hZ w j a hw ha hj
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxVariableSyntax.code true w.castSucc j.castSucc (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxVariables.exists_code hZ true w j hw hjn)
  have hZ1 := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hF1 : Derives Ξ (frame w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc) := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under hF E)
  have hD1 : Derives Ξ (successor D.castSucc depth.castSucc) := of_eq (successor_rename D depth Fin.castSucc) (under hD E)
  have hl1 : Derives Ξ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c e A C K H Fin.castSucc) (under hl E)
  have hU1 : Derives Ξ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under hU E)
  have hV1 : Derives Ξ (SyntaxIdentityMapSyntax.identityMap w.castSucc e.castSucc V.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under hV E)
  have hHead1 : Derives Ξ (SyntaxMixedImageHead.head w.castSucc C.castSucc e.castSucc z.castSucc n.castSucc) := of_eq (SyntaxMixedImageHead.head_rename w C e z n Fin.castSucc) (under hHead E)
  have hi1 : Derives Ξ (Formula.mem i.castSucc A.castSucc) := under hi E
  have hj1 : Derives Ξ (Formula.mem j.castSucc a.castSucc) := under hj E
  have hij1 : Derives Ξ (successor i.castSucc j.castSucc) := of_eq (successor_rename i j Fin.castSucc) (under hij E)
  have hX1 : Derives Ξ (SyntaxVariableSyntax.code true w.castSucc i.castSucc X.castSucc) := of_eq (SyntaxVariableSyntax.code_rename true w i X Fin.castSucc) (under hX E)
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  let B := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc.castSucc R.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise Ξ)
  apply Derives.exE (p := B) (StructuralListFieldValues.exists_value hZ1 w.castSucc R.castSucc j.castSucc hw1 (SyntaxVariableDecode.index_natural true w.castSucc j.castSucc (Fin.last m) (.conjR hE)))
  have hZ2 := ZFContext.under hZ1 B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 B)
  have hF2 : Derives Δ (frame w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := of_eq (frame_rename w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc Fin.castSucc) (under hF1 B)
  have hD2 : Derives Δ (successor D.castSucc.castSucc depth.castSucc.castSucc) := of_eq (successor_rename D.castSucc depth.castSucc Fin.castSucc) (under hD1 B)
  have hl2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc Fin.castSucc) (under hl1 B)
  have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w.castSucc c.castSucc C.castSucc U.castSucc Fin.castSucc) (under hU1 B)
  have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc e.castSucc.castSucc V.castSucc.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w.castSucc e.castSucc V.castSucc Fin.castSucc) (under hV1 B)
  have hHead2 : Derives Δ (SyntaxMixedImageHead.head w.castSucc.castSucc C.castSucc.castSucc e.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc) := of_eq (SyntaxMixedImageHead.head_rename w.castSucc C.castSucc e.castSucc z.castSucc n.castSucc Fin.castSucc) (under hHead1 B)
  have hi2 : Derives Δ (Formula.mem i.castSucc.castSucc A.castSucc.castSucc) := under hi1 B
  have hj2 : Derives Δ (Formula.mem j.castSucc.castSucc a.castSucc.castSucc) := under hj1 B
  have hij2 : Derives Δ (successor i.castSucc.castSucc j.castSucc.castSucc) := of_eq (successor_rename i.castSucc j.castSucc Fin.castSucc) (under hij1 B)
  have hX2 : Derives Δ (SyntaxVariableSyntax.code true w.castSucc.castSucc i.castSucc.castSucc X.castSucc.castSucc) := of_eq (SyntaxVariableSyntax.code_rename true w.castSucc i.castSucc X.castSucc Fin.castSucc) (under hX1 B)
  have hx2 : Derives Δ (SyntaxVariableSyntax.code true w.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename]) (under (.conjR hE) B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := AbstractFrameLiftPoint.bound_at hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc P.castSucc.castSucc D.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc U.castSucc.castSucc V.castSucc.castSucc z.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc X.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc hw2 hF2 hD2 hl2 hU2 hV2 hHead2 hi2 hj2 hij2 hx2 hX2 (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, boundValue_rename, StructuralListFieldSyntax.field_rename]) ho

theorem free {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth P D R S a b c e A C K H U V z n i X q : Fin m)
    (hw : Derives Γ (omega w)) (hF : Derives Γ (frame w mode depth P a b c e R S))
    (hD : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w e V))
    (hHead : Derives Γ (SyntaxMixedImageHead.head w C e z n))
    (hi : Derives Γ (.mem i b)) (hX : Derives Γ (SyntaxVariableSyntax.code false w i X)) :
    Derives Γ ((freeValue w D i q).iff (StructuralListFieldSyntax.field w H i q)) := by
  have hb := Derives.conjL (Derives.conjR (term_lists w mode depth P a b c e R S hF))
  have hin := StructuralListTraceOrder.member_member hZ w i b hw hb hi
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListFieldSyntax.field w.castSucc S.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) (StructuralListFieldValues.exists_value hZ w S i hw hin)
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hF1 : Derives Δ (frame w.castSucc mode.castSucc depth.castSucc P.castSucc a.castSucc b.castSucc c.castSucc e.castSucc R.castSucc S.castSucc) := of_eq (frame_rename w mode depth P a b c e R S Fin.castSucc) (under hF B)
  have hD1 : Derives Δ (successor D.castSucc depth.castSucc) := of_eq (successor_rename D depth Fin.castSucc) (under hD B)
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c e A C K H Fin.castSucc) (under hl B)
  have hU1 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc c.castSucc C.castSucc U.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (under hU B)
  have hV1 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc e.castSucc V.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w e V Fin.castSucc) (under hV B)
  have hHead1 : Derives Δ (SyntaxMixedImageHead.head w.castSucc C.castSucc e.castSucc z.castSucc n.castSucc) := of_eq (SyntaxMixedImageHead.head_rename w C e z n Fin.castSucc) (under hHead B)
  have hi1 : Derives Δ (Formula.mem i.castSucc b.castSucc) := under hi B
  have hX1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc i.castSucc X.castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w i X Fin.castSucc) (under hX B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := AbstractFrameLiftPoint.free_at hZ1 w.castSucc mode.castSucc depth.castSucc P.castSucc D.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc e.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc z.castSucc n.castSucc i.castSucc X.castSucc (Fin.last m) q.castSucc hw1 hF1 hD1 hl1 hU1 hV1 hHead1 hi1 hX1 (.conjR hB)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, freeValue_rename, StructuralListFieldSyntax.field_rename]) ho

end PPAC.Migration.Internal.AbstractFrameLiftValues
