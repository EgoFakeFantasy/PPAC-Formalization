import PPAC.Migration.Internal.OriginalTermScopeElimination

/-! 纯签名项的完整内部作用域桥；以实际恒等／位移／替换列表衔接既有独立项程序。 -/
namespace PPAC.Migration.Internal.OriginalTermProgramBridge
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_on_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth a b c L I R n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTermTraceSyntax.run true w depth L n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R L n q)) := by
  apply OriginalTermScopeElimination.eliminate w a b n _ ht
  intro bound
  let C := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hm1 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc L.castSucc) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth L Fin.castSucc) (under hm C)
  have hI1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I Fin.castSucc) (under hI C)
  have hR1 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc c.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a c Fin.castSucc) (under hR C)
  have hL1 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w b a c L Fin.castSucc) (under hL C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hbranch : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)).conj (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc)) := of_eq
    (by simp only [C, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hC
  have ho := OriginalTermProgramPoint.replace_at_variable hZ1 bound w.castSucc depth.castSucc a.castSucc b.castSucc c.castSucc L.castSucc I.castSucc R.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hm1 hI1 hR1 hL1 (.conjL hbranch) (.conjR hbranch)
  simpa only [Formula.raise, Formula.iff, Formula.rename, OriginalTermTraceSyntax.run_rename, TermTransformProgramSyntax.run_rename] using ho

theorem weaken_on_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth parameter a b B I J R S n q : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) :
    Derives Γ ((OriginalTermTraceSyntax.run false w depth parameter n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  apply OriginalTermScopeElimination.eliminate w a b n _ ht
  intro bound
  let C := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hm1 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc parameter.castSucc) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth parameter Fin.castSucc) (under hm C)
  have hI1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I Fin.castSucc) (under hI C)
  have hJ1 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc b.castSucc B.castSucc J.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J Fin.castSucc) (under hJ C)
  have hR1 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc B.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a B Fin.castSucc) (under hR C)
  have hS1 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc J.castSucc S.castSucc b.castSucc a.castSucc B.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename false w J S b a B Fin.castSucc) (under hS C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hbranch : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc b.castSucc)).conj (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc)) := of_eq
    (by simp only [C, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hC
  have ho := OriginalTermProgramPoint.weaken_at_variable hZ1 bound w.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc B.castSucc I.castSucc J.castSucc R.castSucc S.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hm1 hI1 hJ1 hR1 hS1 (.conjL hbranch) (.conjR hbranch)
  simpa only [Formula.raise, Formula.iff, Formula.rename, OriginalTermTraceSyntax.run_rename, TermTransformProgramSyntax.run_rename] using ho

theorem replace_checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth a b c L I R n q : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L)) :
    Derives Γ ((OriginalTermTraceSyntax.checked true w depth L a b n q).iff
      ((OriginalTermTraceSyntax.metadata w depth L).conj (TermTransformProgramSyntax.checked w R L a b a c n q))) := by
  have henv : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a c R L) := .conjI (IndexTermImageCodeTyping.term_list true w I R a a c hR) hL
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTermTraceSyntax.checked true w depth L a b n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hm := Derives.conjL (Derives.conjL hE)
    have ht := Derives.conjR (Derives.conjL hE)
    have he := replace_on_term (ZFContext.add hZ E) w depth a b c L I R n q (add hw E) hm (add hI E) (add hR E) (add hL E) ht
    exact .conjI hm (.conjI (.conjI (add henv E) ht) (.impE (.conjL he) (.conjR hE)))
  · apply Derives.impI
    let E := (OriginalTermTraceSyntax.metadata w depth L).conj (TermTransformProgramSyntax.checked w R L a b a c n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hm := Derives.conjL hE
    have hp := Derives.conjR hE
    have ht := Derives.conjR (Derives.conjL hp)
    have he := replace_on_term (ZFContext.add hZ E) w depth a b c L I R n q (add hw E) hm (add hI E) (add hR E) (add hL E) ht
    exact .conjI (.conjI hm ht) (.impE (.conjR he) (.conjR hp))

theorem weaken_checked_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth parameter a b B I J R S n q : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B)) :
    Derives Γ ((OriginalTermTraceSyntax.checked false w depth parameter a b n q).iff
      ((OriginalTermTraceSyntax.metadata w depth parameter).conj (TermTransformProgramSyntax.checked w R S a b a B n q))) := by
  have henv : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a B R S) := .conjI (IndexTermImageCodeTyping.term_list true w I R a a B hR) (IndexTermImageCodeTyping.term_list false w J S b a B hS)
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTermTraceSyntax.checked false w depth parameter a b n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hm := Derives.conjL (Derives.conjL hE)
    have ht := Derives.conjR (Derives.conjL hE)
    have he := weaken_on_term (ZFContext.add hZ E) w depth parameter a b B I J R S n q (add hw E) hm (add hI E) (add hJ E) (add hR E) (add hS E) ht
    exact .conjI hm (.conjI (.conjI (add henv E) ht) (.impE (.conjL he) (.conjR hE)))
  · apply Derives.impI
    let E := (OriginalTermTraceSyntax.metadata w depth parameter).conj (TermTransformProgramSyntax.checked w R S a b a B n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hm := Derives.conjL hE
    have hp := Derives.conjR hE
    have ht := Derives.conjR (Derives.conjL hp)
    have he := weaken_on_term (ZFContext.add hZ E) w depth parameter a b B I J R S n q (add hw E) hm (add hI E) (add hJ E) (add hR E) (add hS E) ht
    exact .conjI (.conjI hm ht) (.impE (.conjR he) (.conjR hp))

theorem replace_coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth a b c L I R n q : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L)) :
    Derives Γ ((OriginalTermTraceSyntax.checked true w depth L a b n q).iff
      ((OriginalTermTraceSyntax.metadata w depth L).conj (SyntaxCodedMixedTermSyntax.substituted w R L a b a c n q))) :=
  SyntaxTypeLocalTransfer.iff_trans (replace_checked_iff hZ w depth a b c L I R n q hw hI hR hL)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (TermTransformProgramCorrectness.checked_iff hZ w R L a b a c n q hw))

theorem weaken_coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w depth parameter a b B I J R S n q : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (hR : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B)) :
    Derives Γ ((OriginalTermTraceSyntax.checked false w depth parameter a b n q).iff
      ((OriginalTermTraceSyntax.metadata w depth parameter).conj (SyntaxCodedMixedTermSyntax.substituted w R S a b a B n q))) :=
  SyntaxTypeLocalTransfer.iff_trans (weaken_checked_iff hZ w depth parameter a b B I J R S n q hw hI hJ hR hS)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (TermTransformProgramCorrectness.checked_iff hZ w R S a b a B n q hw))

end PPAC.Migration.Internal.OriginalTermProgramBridge
