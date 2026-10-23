import PPAC.Migration.Internal.AtomicTermAgreementSyntax

/-! 实际mode0／3项环境推导整个内部受检项程序agreement，不添加比较公理。 -/
namespace PPAC.Migration.Internal.AtomicTermAgreement
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L)) :
    Derives Γ (AtomicTermAgreementSyntax.agreement w mode depth L R L a b a c) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two h A
  have h02 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift h0)
  have h12 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (lift h1)
  have h22 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc depth.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (lift h2)
  have h32 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc a.castSucc.castSucc I.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]) (lift h3)
  have h42 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (lift h4)
  have h52 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (lift h5)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hOriginal := OriginalNumericTermProgram.replace_on_term hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) h02 h12 h22 h32 h42 h52 hA
  have hR := IndexTermImageCodeTyping.term_list true _ _ _ _ _ _ h42
  have hMaps : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc R.castSucc.castSucc L.castSucc.castSucc) := .conjI hR h52
  have hChecked := AtomicTermAgreementSyntax.checked_iff_run w.castSucc.castSucc R.castSucc.castSucc L.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hMaps hA
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal (.conjI (.conjR hChecked) (.conjL hChecked))

theorem weaken_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B)) :
    Derives Γ (AtomicTermAgreementSyntax.agreement w mode depth parameter R S a b a B) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxTermSyntax.term w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two h A
  have h02 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift h0)
  have h12 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (lift h1)
  have h22 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (lift h2)
  have h32 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc a.castSucc.castSucc I.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]) (lift h3)
  have h42 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc J.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftCode_rename]) (lift h4)
  have h52 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (lift h5)
  have h62 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc.castSucc J.castSucc.castSucc S.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (lift h6)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  have hOriginal := OriginalNumericTermProgram.weaken_on_term hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) h02 h12 h22 h32 h42 h52 h62 hA
  have hR := IndexTermImageCodeTyping.term_list true _ _ _ _ _ _ h52
  have hS := IndexTermImageCodeTyping.term_list false _ _ _ _ _ _ h62
  have hMaps : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc) := .conjI hR hS
  have hChecked := AtomicTermAgreementSyntax.checked_iff_run w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hMaps hA
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal (.conjI (.conjR hChecked) (.conjL hChecked))

end PPAC.Migration.Internal.AtomicTermAgreement
