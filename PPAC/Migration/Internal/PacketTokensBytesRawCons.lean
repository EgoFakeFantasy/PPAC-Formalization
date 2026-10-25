import PPAC.Migration.Internal.PacketTokensBytesRecursionEquation

/-! Actual original Cons injectivity aligns the independent coupled trace to every given prefix Cons. -/
namespace PPAC.Migration.Internal.PacketTokensBytesRawCons
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokensBytesSyntax
open SyntaxRenameQuerySyntax (of_eq)

def remaining {m} (w h x t a : Fin m) : Formula m := .ex
  ((raw w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc))

theorem remaining_rename {m k} (w h x t a : Fin m) (ρ : Fin m → Fin k) :
    (remaining w h x t a).rename ρ = remaining (ρ w) (ρ h) (ρ x) (ρ t) (ρ a) := by
  simp only [remaining,Formula.rename,raw_rename,PacketTokensBytesRowSyntax.push_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_remaining {m} {Γ : Context m} (w h x t a u : Fin m) (hf : Derives Γ (raw w x t u))
    (hp : Derives Γ (PacketTokensBytesRowSyntax.push w h u a)) : Derives Γ (remaining w h x t a) := by
  apply Derives.exI u
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,raw_rename,PacketTokensBytesRowSyntax.push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hf hp)

theorem values {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a d y u : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hd : Derives Γ (StructuralListSyntax.consCode w d y s))
    (hf : Derives Γ (raw w y t u)) (hp : Derives Γ (PacketTokensBytesRowSyntax.push w d u a)) : Derives Γ (remaining w h x t a) := by
  have hy := StructuralListValidity.range w y (.conjL (PacketTokensBytesTraceBase.domain w y t u hf))
  have he := StructuralConsUnique.injective hZ w h x d y s hw hh hx (.conjL hp) hy hc hd
  have hfX := PacketTokensBytesTraceTransport.input_subst w y t u x (eq_symm (.conjR he)) hf
  have hpH := PacketTokensBytesPushTransport.head w d h u a (eq_symm (.conjL he)) hp
  exact intro_remaining w h x t a u hfX hpH

theorem actual_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s))
    (hf : Derives Γ (PacketTokensBytesRecursionSyntax.consCase w s t a)) : Derives Γ (remaining w h x t a) := by
  let R := PacketTokensBytesRecursionSyntax.consBody w s t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hc3 := of_eq (StructuralListSyntax.consCode_rename w h x s (old 3)) (HornBinderRules.under_body 3 hc R)
  exact of_eq (remaining_rename w h x t a (old 3)).symm
    (values hZ3 (old 3 w) (old 3 h) (old 3 x) (old 3 s) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2)
      hw3 (HornBinderRules.under_body 3 hh R) (HornBinderRules.under_body 3 hx R) hc3 (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR)))

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hx : Derives Γ (.mem x w))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x s)) (hf : Derives Γ (raw w s t a)) : Derives Γ (remaining w h x t a) := by
  have he := Derives.impE (.conjL (PacketTokensBytesRecursionEquation.fold_iff hZ w s t a hw)) hf
  apply Derives.disjE he
  · exact .botE (StructuralConsUnique.disjoint (ZFContext.add hZ _) w h x s (add hw _) (.conjL (.hyp (Or.inl rfl))) (add hc _))
  · exact actual_case (ZFContext.add hZ _) w h x s t a (add hw _) (add hh _) (add hx _) (add hc _) (.hyp (Or.inl rfl))

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h x s t a : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (StructuralListSyntax.consCode w h x s))
    (hr : Derives Γ (remaining w h x t a)) : Derives Γ (raw w s t a) := by
  let R := (raw w.castSucc x.castSucc t.castSucc (Fin.last m)).conj
    (PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) a.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h x s Fin.castSucc) (under hc R)
  simpa only [Formula.raise,raw_rename] using PacketTokensBytesTraceAppend.cons_fold hZ1 _ _ _ _ _ _ _ hw1 (.conjL hR) hc1 (.conjR hR)

end PPAC.Migration.Internal.PacketTokensBytesRawCons
