import PPAC.Migration.Internal.SyntaxComposeLiftCode

/-! 任意内部输出码下的提升/复合识别双条件，以及独立中间后继的原等词对齐。 -/
namespace PPAC.Migration.Internal.SyntaxComposeLiftCodeLaws
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxComposeCodeSyntax
open SyntaxMapLiftSyntax (codedLift codedLift_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem output_subst {m} {Γ : Context m} (w a e K A E L M : Fin m)
    (he : Derives Γ (.equal L M)) (hl : Derives Γ (codedLift w a e K A E L)) : Derives Γ (codedLift w a e K A E M) := by
  let P := codedLift w.castSucc a.castSucc e.castSucc K.castSucc A.castSucc E.castSucc (Fin.last m)
  have e0 : P.instantiate L = codedLift w a e K A E L := by simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate M = codedLift w a e K A E M := by simp only [P, Formula.instantiate, codedLift_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hl))

theorem coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T K A C E Lr Lt Lk : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (coded w a c e R T K))
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T C E Lt)) :
    Derives Γ ((codedLift w a e K A E Lk).iff (coded w A C E Lr Lt Lk)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact SyntaxComposeLiftCode.composition (ZFContext.add hZ _) w a c e R T K A C E Lr Lt Lk (add hw _) (add hc _) (add hr _) (add ht _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    let D := coded w A C E Lr Lt Lk
    have hp := SyntaxMapLiftParameters.successors w a c R A C Lr hr
    have hq := SyntaxMapLiftParameters.successors w c e T C E Lt ht
    have hx := SyntaxMapLift.exists_code (ZFContext.add hZ D) w a e K A E (add hw D)
      (add (SyntaxComposeCodeReadback.output_code w a c e R T K hc) D) (add (.conjL hp) D) (add (.conjR hq) D)
    let P := codedLift w.castSucc a.castSucc e.castSucc K.castSucc A.castSucc E.castSucc (Fin.last m)
    let Δ := Context.add P (Context.image Formula.raise (Context.add D Γ))
    apply Derives.exE (p := P) hx
    have hZ1 := ZFContext.under (ZFContext.add hZ D) P
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under (add hw D) P)
    have hc1 : Derives Δ (coded w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc K.castSucc) := of_eq (coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add hc D) P)
    have hr1 : Derives Δ (codedLift w.castSucc a.castSucc c.castSucc R.castSucc A.castSucc C.castSucc Lr.castSucc) := of_eq (codedLift_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add hr D) P)
    have ht1 : Derives Δ (codedLift w.castSucc c.castSucc e.castSucc T.castSucc C.castSucc E.castSucc Lt.castSucc) := of_eq (codedLift_rename _ _ _ _ _ _ _ Fin.castSucc) (under (add ht D) P)
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hM := SyntaxComposeLiftCode.composition hZ1 w.castSucc a.castSucc c.castSucc e.castSucc R.castSucc T.castSucc K.castSucc A.castSucc C.castSucc E.castSucc Lr.castSucc Lt.castSucc (Fin.last m) hw1 hc1 hr1 ht1 hP
    have hD1 : Derives Δ (coded w.castSucc A.castSucc C.castSucc E.castSucc Lr.castSucc Lt.castSucc Lk.castSucc) := of_eq (coded_rename _ _ _ _ _ _ _ Fin.castSucc) (under (Derives.hyp (Or.inl rfl) : Derives (Context.add D Γ) D) P)
    have heq := SyntaxComposeCodeUnique.unique hZ1 w.castSucc A.castSucc C.castSucc E.castSucc Lr.castSucc Lt.castSucc (Fin.last m) Lk.castSucc hw1 hM hD1
    exact of_eq (codedLift_rename w a e K A E Lk Fin.castSucc).symm (output_subst _ _ _ _ _ _ _ _ heq hP)

theorem middle_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T A C D E Lr Lt : Fin m)
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T D E Lt)) : Derives Γ (.equal C D) := by
  have hp := SyntaxMapLiftParameters.successors w a c R A C Lr hr
  have hq := SyntaxMapLiftParameters.successors w c e T D E Lt ht
  exact InsertLogic.unique C D c c (ZFContext.arithmetic hZ).base.extensionality (.conjR hp) (.conjL hq)

theorem mixed_middle {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T K A C D E Lr Lt Lk : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (coded w a c e R T K))
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T D E Lt))
    (hk : Derives Γ (codedLift w a e K A E Lk)) : Derives Γ ((Formula.equal C D).conj (coded w A C E Lr Lt Lk)) := by
  have he := middle_equal hZ w a c e R T A C D E Lr Lt hr ht
  have ht' := SyntaxMapLiftParameters.subst_u w c e T D E Lt C (eq_symm he) ht
  exact .conjI he (SyntaxComposeLiftCode.composition hZ w a c e R T K A C E Lr Lt Lk hw hc hr ht' hk)

theorem mixed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c e R T K A C D E Lr Lt Lk : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (coded w a c e R T K))
    (hr : Derives Γ (codedLift w a c R A C Lr)) (ht : Derives Γ (codedLift w c e T D E Lt)) :
    Derives Γ ((Formula.equal C D).conj ((codedLift w a e K A E Lk).iff (coded w A C E Lr Lt Lk))) := by
  have he := middle_equal hZ w a c e R T A C D E Lr Lt hr ht
  have ht' := SyntaxMapLiftParameters.subst_u w c e T D E Lt C (eq_symm he) ht
  exact .conjI he (coded_iff hZ w a c e R T K A C E Lr Lt Lk hw hc hr ht')
end PPAC.Migration.Internal.SyntaxComposeLiftCodeLaws
