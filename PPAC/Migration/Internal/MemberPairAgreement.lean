import PPAC.Migration.Internal.MemberPairAgreementSyntax

/-! 实际mode0／3环境在所有内部源／目标参数码上消去两参数agreement前提。 -/
namespace PPAC.Migration.Internal.MemberPairAgreement
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem replace_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ (MemberPairAgreementSyntax.agreement w mode depth L R L a c x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxForestSyntax.forest 2 w.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc) (Fin.last m).castSucc
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := ZFContext.under_two hZ A
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := OrderedPairElimination.under_two h A
  have h02 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift h0)
  have h12 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (lift h1)
  have h22 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc depth.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (lift h2)
  have h32 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc a.castSucc.castSucc I.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]) (lift h3)
  have h42 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc a.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.converted_rename]) (lift h4)
  have h52 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termList_rename]) (lift h5)
  have hT2 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (lift hT)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact OriginalArgumentPairProgram.replace_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc I.castSucc.castSucc R.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc h02 h12 h22 h32 h42 h52 hA hT2

theorem weaken_agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S a B x y) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := SyntaxForestSyntax.forest 2 w.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc) (Fin.last m).castSucc
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
  have hT2 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (SyntaxAtomSyntax.two x.castSucc.castSucc y.castSucc.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (lift hT)
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact OriginalArgumentPairProgram.weaken_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc h02 h12 h22 h32 h42 h52 h62 hA hT2

end PPAC.Migration.Internal.MemberPairAgreement
