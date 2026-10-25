import PPAC.Migration.Internal.StructuralListSpliceRawCons

/-! The public splice relation retains actual tail/joined validity and has exact original Nil/Cons equations on all internal candidates. -/
namespace PPAC.Migration.Internal.StructuralListSplice
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSpliceSyntax
open SyntaxRenameQuerySyntax (of_eq)

def remaining {m} (w h x t a : Fin m) : Formula m := .ex
  ((splice w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) a.castSucc))

theorem remaining_rename {m k} (w h x t a : Fin m) (ρ : Fin m → Fin k) :
    (remaining w h x t a).rename ρ = remaining (ρ w) (ρ h) (ρ x) (ρ t) (ρ a) := by
  simp only [remaining,Formula.rename,splice_rename,StructuralListSyntax.consCode_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem tail_valid {m} {Γ : Context m} (w n t a : Fin m) (hs : Derives Γ (splice w n t a)) :
    Derives Γ (StructuralListTraceSyntax.valid w t) := .conjL hs

theorem joined_valid {m} {Γ : Context m} (w n t a : Fin m) (hs : Derives Γ (splice w n t a)) :
    Derives Γ (StructuralListTraceSyntax.valid w a) := .conjL (.conjR hs)

theorem prefix_valid {m} {Γ : Context m} (w n t a : Fin m) (hs : Derives Γ (splice w n t a)) :
    Derives Γ (StructuralListTraceSyntax.valid w n) := .conjL (StructuralListSpliceTraceBase.domain _ _ _ _ (.conjR (.conjR hs)))

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ ((splice w n t a).iff ((StructuralListTraceSyntax.valid w t).conj (.equal t a))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hS : Derives (Context.add (splice w n t a) Γ) (splice w n t a) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hS) (StructuralListSpliceTraceBase.nil_value (ZFContext.add hZ _) _ _ _ _ (add hw _) (add hn _) (.conjR (.conjR hS)))
  · apply Derives.impI
    let H := (StructuralListTraceSyntax.valid w t).conj (.equal t a)
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hA := StructuralListTraceSyntax.output_subst _ _ _ (.conjR hH) (.conjL hH)
    have hRaw := StructuralListSpliceTraceBase.nil_fold (ZFContext.add hZ H) w n t (add hw H) (add hn H) (StructuralListValidity.range _ _ (.conjL hH))
    exact .conjI (.conjL hH) (.conjI hA (StructuralListSpliceTraceTransport.output_subst _ _ _ _ _ (.conjR hH) hRaw))

theorem intro_remaining {m} {Γ : Context m} (w h x t a u : Fin m) (hs : Derives Γ (splice w x t u))
    (hc : Derives Γ (StructuralListSyntax.consCode w h u a)) : Derives Γ (remaining w h x t a) := by
  apply Derives.exI u
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,splice_rename,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hs hc)

theorem cons_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hs : Derives Γ (splice w s t a)) : Derives Γ (remaining w h x t a) := by
  let R := (raw w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (StructuralListSpliceRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListSpliceRawCons.forward hZ w h x s t a hw hh hx hc (.conjR (.conjR hs)))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hTail := of_eq (StructuralListTraceSyntax.valid_rename w t Fin.castSucc) (under (.conjL hs) R)
  have hA := of_eq (StructuralListTraceSyntax.valid_rename w a Fin.castSucc) (under (.conjL (.conjR hs)) R)
  have huN := Derives.conjR (.conjR (StructuralListSpliceTraceBase.domain _ _ _ _ (.conjL hR)))
  have hCons := Derives.conjR (.conjR hR)
  have huV := StructuralListDecode.tail_valid hZ1 _ _ _ _ hw1 hh1 huN hCons hA
  have hSmall : Derives Δ (splice w.castSucc x.castSucc t.castSucc (Fin.last m)) := .conjI hTail (.conjI huV (.conjL hR))
  simpa only [Formula.raise,remaining_rename] using intro_remaining _ _ _ _ _ _ hSmall hCons

theorem cons_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hc : Derives Γ (StructuralListSyntax.consCode w h x s))
    (hr : Derives Γ (remaining w h x t a)) : Derives Γ (splice w s t a) := by
  let R := (splice w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (StructuralListSyntax.consCode w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hh1 : Derives Δ (.mem h.castSucc w.castSucc) := under hh R
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x s Fin.castSucc) (under hc R)
  have hSmall := Derives.conjL hR
  have hA := StructuralListValidity.cons_valid hZ1 _ _ _ _ hw1 hh1 (.conjL (.conjR hSmall)) (.conjR hR)
  have hPush : Derives Δ (StructuralListSpliceRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc) := .conjI hh1 (.conjR hR)
  have hRaw := StructuralListSpliceTraceAppend.cons_fold hZ1 _ _ _ _ _ _ _ hw1 (.conjR (.conjR hSmall)) hc1 hPush
  have hout : Derives Δ (splice w.castSucc s.castSucc t.castSucc a.castSucc) := .conjI (.conjL hSmall) (.conjI hA hRaw)
  simpa only [Formula.raise,splice_rename] using hout

theorem cons_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) :
    Derives Γ ((splice w s t a).iff (remaining w h x t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact cons_forward (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hh _) (add hx _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact cons_backward (ZFContext.add hZ _) _ _ _ _ _ _ (add hw _) (add hh _) (add hc _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.StructuralListSplice
