import PPAC.Migration.Internal.PureSyntaxArgumentPremises

/-! 原cons矩阵的对象健全性：尾码严格成员归纳及实际前提恢复。 -/
namespace PPAC.Migration.Internal.PureSyntaxConsSound
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PureSyntaxConsRule PureSyntaxListInductionSyntax
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation

theorem contexts_subst {m} {Γ : Context m} (w k b f B F n : Fin m)
    (hb : Derives Γ (.equal B b)) (hf : Derives Γ (.equal F f))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k B F n)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  let P := SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc (Fin.last m) F.castSucc n.castSucc
  have h0 : P.instantiate B = SyntaxMixedImageCodeSyntax.termList w k B F n := by simp only [P, Formula.instantiate, SyntaxMixedImageCodeSyntax.termList_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate b = SyntaxMixedImageCodeSyntax.termList w k b F n := by simp only [P, Formula.instantiate, SyntaxMixedImageCodeSyntax.termList_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hp := of_eq h1 (Derives.eqSubst P hb (of_eq h0.symm ht))
  let Q := SyntaxMixedImageCodeSyntax.termList w.castSucc k.castSucc b.castSucc (Fin.last m) n.castSucc
  have h2 : Q.instantiate F = SyntaxMixedImageCodeSyntax.termList w k b F n := by simp only [Q, Formula.instantiate, SyntaxMixedImageCodeSyntax.termList_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h3 : Q.instantiate f = SyntaxMixedImageCodeSyntax.termList w k b f n := by simp only [Q, Formula.instantiate, SyntaxMixedImageCodeSyntax.termList_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h3 (Derives.eqSubst Q hf (of_eq h2.symm hp))

theorem matrix_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r R : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hi : Derives Γ (allIH w n)) (hs : Derives Γ (RestrictionSyntax.subset R w))
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (hm : Derives Γ (HornRuleSyntax.matrix ObjectTermSyntax.consRule w r R env)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  have hg := Derives.conjL hm
  rw [actual_head] at hg
  have h0 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 0 hw hn hg hr
  have h1 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 1 hw hn hg hr
  have h2 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 2 hw hn hg hr
  have h3 := HornNodeFields.field_4 hZ 1 fields w r env (PureSyntaxTrace.four b f k n) 3 hw hn hg hr
  have hv (i : Fin 5) : Derives Γ (graph (.var i) w env (env i)) := .conjI (environmentNat_at w env hn i) (.eqRefl _)
  have hsuccessor := PureSyntaxArgumentPremises.succ_variable (2 : Fin 5) w k env h2
  have hcons := Derives.impE (.conjL (HornExprStructural.cons_iff hZ (.var 3) (.var 4) w (env 3) (env 4) n env hw hn (hv 3) (hv 4))) h3
  have hp : Derives Γ (HornRuleSyntax.premise (Expr.node (.literal 0) (List.ofFn headFields)) w R env) := .conjL (.conjR (.conjR hm))
  have hq : Derives Γ (HornRuleSyntax.premise (Expr.node (.literal 1) (List.ofFn tailFields)) w R env) := .conjL (.conjR (.conjR (.conjR hm)))
  have hhead := PureSyntaxArgumentPremises.head_term hZ w R env hw hn hc hp
  have htail := PureSyntaxArgumentPremises.tail_checked hZ w R env hw hn hs hc hq
  have hless := Derives.conjR (StructuralConsCore.components hZ w (env 3) (env 4) n hw (environmentNat_at w env hn 3) (environmentNat_at w env hn 4) hcons)
  have hcorrect := correct_at w (env 4) (env 0) (env 1) (env 2) (allIH_at w n (env 4) hi hless)
  have htyped := Derives.impE (.conjL hcorrect) htail
  have hout := TypedArgumentListConstruction.cons_list hZ w (env 2) k (env 0) (env 1) (env 3) (env 4) n hw hhead htyped hcons hsuccessor
  exact contexts_subst w k b f (env 0) (env 1) n (eq_symm (.conjR h0)) (eq_symm (.conjR h1)) hout

theorem application_sound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b f k n r R : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH w n))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (PureSyntaxTrace.closed w R))
    (hr : Derives Γ (PureSyntaxTrace.argumentRow w b f k n r))
    (ha : Derives Γ (HornApplicationSyntax.application ObjectTermSyntax.consRule w r R)) :
    Derives Γ (SyntaxMixedImageCodeSyntax.termList w k b f n) := by
  let B := HornApplicationSyntax.body ObjectTermSyntax.consRule w r R
  let Δ := Context.add B (raisedContext 5 Γ)
  apply HornApplicationRules.eliminate_application ObjectTermSyntax.consRule w r R _ ha
  have hw1 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw B)
  have hi1 : Derives Δ (allIH (old 5 w) (old 5 n)) := of_eq (allIH_rename w n (old 5)) (HornBinderRules.under_body 5 hi B)
  have hs1 : Derives Δ (RestrictionSyntax.subset (old 5 R) (old 5 w)) := of_eq (RestrictionSyntax.subset_rename R w (old 5)) (HornBinderRules.under_body 5 hs B)
  have hc1 : Derives Δ (PureSyntaxTrace.closed (old 5 w) (old 5 R)) := of_eq (PureSyntaxTrace.closed_rename w R (old 5)) (HornBinderRules.under_body 5 hc B)
  have hr1 : Derives Δ (PureSyntaxTrace.argumentRow (old 5 w) (old 5 b) (old 5 f) (old 5 k) (old 5 n) (old 5 r)) := of_eq (PureSyntaxTrace.argumentRow_rename w b f k n r (old 5)) (HornBinderRules.under_body 5 hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := matrix_sound (HornBinderRules.zf_body 5 hZ B) _ _ _ _ _ _ _ (slot 5) hw1 (.conjL hB) hi1 hs1 hc1 hr1 (.conjR (.conjR hB))
  exact of_eq (SyntaxMixedImageCodeSyntax.termList_rename w k b f n (old 5)).symm ht

end PPAC.Migration.Internal.PureSyntaxConsSound
