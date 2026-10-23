import PPAC.Migration.Internal.OriginalNumericTermValueTransfer

/-! 原模式0／3实际有类型唯一输出；比较前提由实际环境正式消去。 -/
namespace PPAC.Migration.Internal.OriginalNumericTermFiber
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalNumericTermValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R n : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (h6 : Derives Γ (SyntaxTermSyntax.term w a b n))
    : Derives Γ (agreement w mode depth L R L n) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have g0 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc h0)
  have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (Derives.rename Fin.castSucc h1)
  have g2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc L.castSucc) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (Derives.rename Fin.castSucc h2)
  have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (Derives.rename Fin.castSucc h3)
  have g4 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc c.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (Derives.rename Fin.castSucc h4)
  have g5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (Derives.rename Fin.castSucc h5)
  have g6 : Derives Δ (SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (by simp only [SyntaxTermSyntax.term_rename]) (Derives.rename Fin.castSucc h6)
  exact OriginalNumericTermProgram.replace_on_term (ZFContext.rename hZ Fin.castSucc) w.castSucc mode.castSucc depth.castSucc a.castSucc b.castSucc c.castSucc L.castSucc I.castSucc R.castSucc n.castSucc (Fin.last m) g0 g1 g2 g3 g4 g5 g6

theorem replace_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R n : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (h6 : Derives Γ (SyntaxTermSyntax.term w a b n))
    : Derives Γ (fiber w mode depth L a c n) := by
  have henv : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a c R L) := .conjI (IndexTermImageCodeTyping.term_list true w I R a a c h4) h5
  have hf := TermTransformProgramValue.actual_fiber hZ w R L a b a c n h0 (.conjI henv h6)
  exact OriginalNumericTermValueTransfer.fiber_of_program w mode depth L R L a b a c n
    (replace_agreement hZ w mode depth a b c L I R n h0 h1 h2 h3 h4 h5 h6) hf

theorem weaken_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S n : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (h7 : Derives Γ (SyntaxTermSyntax.term w a b n))
    : Derives Γ (agreement w mode depth parameter R S n) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have g0 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc h0)
  have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (Derives.rename Fin.castSucc h1)
  have g2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc parameter.castSucc) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (Derives.rename Fin.castSucc h2)
  have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (Derives.rename Fin.castSucc h3)
  have g4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc b.castSucc B.castSucc J.castSucc) := of_eq (by simp only [SyntaxFreeShiftSyntax.shiftCode_rename]) (Derives.rename Fin.castSucc h4)
  have g5 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc B.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (Derives.rename Fin.castSucc h5)
  have g6 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc J.castSucc S.castSucc b.castSucc a.castSucc B.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (Derives.rename Fin.castSucc h6)
  have g7 : Derives Δ (SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc n.castSucc) := of_eq (by simp only [SyntaxTermSyntax.term_rename]) (Derives.rename Fin.castSucc h7)
  exact OriginalNumericTermProgram.weaken_on_term (ZFContext.rename hZ Fin.castSucc) w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc B.castSucc I.castSucc J.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) g0 g1 g2 g3 g4 g5 g6 g7

theorem weaken_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S n : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (h7 : Derives Γ (SyntaxTermSyntax.term w a b n))
    : Derives Γ (fiber w mode depth parameter a B n) := by
  have henv : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b a B R S) := .conjI (IndexTermImageCodeTyping.term_list true w I R a a B h5) (IndexTermImageCodeTyping.term_list false w J S b a B h6)
  have hf := TermTransformProgramValue.actual_fiber hZ w R S a b a B n h0 (.conjI henv h7)
  exact OriginalNumericTermValueTransfer.fiber_of_program w mode depth parameter R S a b a B n
    (weaken_agreement hZ w mode depth parameter a b B I J R S n h0 h1 h2 h3 h4 h5 h6 h7) hf

theorem replace_promise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth a b c L I R : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    : Derives Γ (promise w mode depth L a b a c) := by
  apply Derives.allI
  apply Derives.impI
  let E := SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have g0 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under h0 E)
  have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (under h1 E)
  have g2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc L.castSucc) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (under h2 E)
  have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (under h3 E)
  have g4 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc c.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (under h4 E)
  have g5 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc) := of_eq (by simp only [SyntaxMixedImageCodeSyntax.termList_rename]) (under h5 E)
  exact replace_fiber (ZFContext.under hZ E) w.castSucc mode.castSucc depth.castSucc a.castSucc b.castSucc c.castSucc L.castSucc I.castSucc R.castSucc (Fin.last m) g0 g1 g2 g3 g4 g5 (.hyp (Or.inl rfl))

theorem weaken_promise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode depth parameter a b B I J R S : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    : Derives Γ (promise w mode depth parameter a b a B) := by
  apply Derives.allI
  apply Derives.impI
  let E := SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have g0 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under h0 E)
  have g1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (under h1 E)
  have g2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc parameter.castSucc) := of_eq (by simp only [OriginalTermTraceSyntax.metadata_rename]) (under h2 E)
  have g3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (by simp only [SyntaxIdentityMapSyntax.identityCode_rename]) (under h3 E)
  have g4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc b.castSucc B.castSucc J.castSucc) := of_eq (by simp only [SyntaxFreeShiftSyntax.shiftCode_rename]) (under h4 E)
  have g5 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc B.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (under h5 E)
  have g6 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc J.castSucc S.castSucc b.castSucc a.castSucc B.castSucc) := of_eq (by simp only [IndexTermImageCodeSyntax.converted_rename]) (under h6 E)
  exact weaken_fiber (ZFContext.under hZ E) w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc B.castSucc I.castSucc J.castSucc R.castSucc S.castSucc (Fin.last m) g0 g1 g2 g3 g4 g5 g6 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalNumericTermFiber
