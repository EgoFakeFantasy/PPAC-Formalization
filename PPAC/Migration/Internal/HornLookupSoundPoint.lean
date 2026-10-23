import PPAC.Migration.Internal.HornLookupTailSound

/-! 完整原规则表闭合性与真实量化lookup应用逐点闭合对象成员归纳性质。 -/
namespace PPAC.Migration.Internal.HornLookupSoundPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupSoundSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (closed w R)) (he : Derives Γ (earlier w R n))
    (hr : Derives Γ (row w n i y r)) (hm : Derives Γ (.mem r R)) : Derives Γ (LookupTableExecutionSyntax.executed w n i y) := by
  have hs := closed_at w R r hc hm
  have hd := Derives.impE (.conjL (OriginalLookupDispatch.dispatch_iff hZ 3 w r R (OriginalLookupExpr.rowFields n i y) hw hr)) hs
  apply Derives.disjE hd
  · exact HornLookupHeadSound.application_execution (ZFContext.add hZ _) w n i y r R (add hw _) (add hr _) (.hyp (Or.inl rfl))
  · exact HornLookupTailSound.application_execution (ZFContext.add hZ _) w n i y r R (add hw _) (add hr _) (add he _) (.hyp (Or.inl rfl))

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (closed w R)) (he : Derives Γ (earlier w R n)) :
    Derives Γ (property w R n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (row w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
    (.mem (Fin.last (m+2)) R.castSucc.castSucc.castSucc)
  let Δ := Context.add A (HornBinderSyntax.raisedContext 3 Γ)
  have hZ3 := HornBinderRules.zf_body 3 hZ A
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w (HornBinderSyntax.old 3)) (HornBinderRules.under_body 3 hw A)
  have hc3 : Derives Δ (closed w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc) := of_eq (closed_rename w R (HornBinderSyntax.old 3)) (HornBinderRules.under_body 3 hc A)
  have he3 : Derives Δ (earlier w.castSucc.castSucc.castSucc R.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (earlier_rename w R n (HornBinderSyntax.old 3)) (HornBinderRules.under_body 3 he A)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact execution hZ3 _ _ _ _ _ _ hw3 hc3 he3 (.conjL hA) (.conjR hA)

end PPAC.Migration.Internal.HornLookupSoundPoint
