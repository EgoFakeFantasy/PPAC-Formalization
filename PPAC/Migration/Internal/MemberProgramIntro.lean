import PPAC.Migration.Internal.MemberProgramOutput

/-! 从独立成员输出实际构造原参数森林及编号0，逐个对象存在见证正式消去。 -/
namespace PPAC.Migration.Internal.MemberProgramIntro
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_arguments {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y q X Y A T z : Fin m)
    (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w c d (SyntaxAtomSyntax.two X Y)))
    (hm : Derives Γ (SyntaxAtomSyntax.memberCode w s X Y q))
    (hr : Derives Γ (ArgumentForestProgramSyntax.runs 2 w R S (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two X Y)))
    (hFA : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) A))
    (hFT : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two X Y) T))
    (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)) :
    Derives Γ (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q) := by
  have hPair := ArgumentPairProgramSyntax.intro_returned w R S c d x y T X Y ht hFT hr
  have hAgreement := MemberPairAgreementSyntax.agreement_at w mode depth parameter R S c d x y A T ha hFA
  have hRaw := Derives.impE (.conjR hAgreement) hPair
  have hApp := Derives.impE (.conjR (OriginalFormulaMemberApplication.member_at_forest_iff hZ w z s X Y T q hw hz hs hFT)) hm
  exact OriginalFormulaMemberCaseSyntax.intro_case w mode depth parameter x y q z A T hz hFA hApp hRaw

theorem at_forests {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y q X Y A T : Fin m)
    (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w c d (SyntaxAtomSyntax.two X Y)))
    (hm : Derives Γ (SyntaxAtomSyntax.memberCode w s X Y q))
    (hr : Derives Γ (ArgumentForestProgramSyntax.runs 2 w R S (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two X Y)))
    (hFA : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) A))
    (hFT : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two X Y) T)) :
    Derives Γ (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 0 (Fin.last m))
  have he := SyntaxNumerals.exists_numeral hZ 0 w hw
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w.castSucc s.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]) (under hs B)
  have ha1 : Derives Δ (MemberPairAgreementSyntax.agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc x.castSucc y.castSucc) := of_eq (by simp only [Formula.raise, MemberPairAgreementSyntax.agreement_rename]) (under ha B)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc c.castSucc d.castSucc (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht B)
  have hm1 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc s.castSucc X.castSucc Y.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (under hm B)
  have hr1 : Derives Δ (ArgumentForestProgramSyntax.runs 2 w.castSucc R.castSucc S.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.runs_rename, SyntaxAtomSyntax.two_map]) (under hr B)
  have hFA1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) A.castSucc) := of_eq (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hFA B)
  have hFT1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two X.castSucc Y.castSucc) T.castSucc) := of_eq (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hFT B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOut := at_arguments hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc s.castSucc x.castSucc y.castSucc q.castSucc X.castSucc Y.castSucc A.castSucc T.castSucc (Fin.last m) hw1 hs1 ha1 ht1 hm1 hr1 hFA1 hFT1 (.conjR hB)
  exact of_eq (OriginalFormulaMemberCaseSyntax.membershipCase_rename w mode depth parameter x y q Fin.castSucc).symm hOut

theorem at_source_arguments {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y q X Y A : Fin m)
    (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w c d (SyntaxAtomSyntax.two X Y)))
    (hm : Derives Γ (SyntaxAtomSyntax.memberCode w s X Y q))
    (hr : Derives Γ (ArgumentForestProgramSyntax.runs 2 w R S (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two X Y)))
    (hFA : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) A)) :
    Derives Γ (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two X.castSucc Y.castSucc) (Fin.last m))
  have hInputs := SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two X Y) (fun i => SyntaxTerms.range hZ w c d _ hw (ArgumentForestProgramSyntax.typed_at 2 w c d _ ht i))
  have he : Derives Γ (.ex B) := of_eq (by simp only [B, SyntaxForestSyntax.existsForest, SyntaxAtomSyntax.two_map]) (SyntaxForests.exists_forest hZ 2 w (SyntaxAtomSyntax.two X Y) hw hInputs)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w.castSucc s.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]) (under hs B)
  have ha1 : Derives Δ (MemberPairAgreementSyntax.agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc x.castSucc y.castSucc) := of_eq (by simp only [Formula.raise, MemberPairAgreementSyntax.agreement_rename]) (under ha B)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc c.castSucc d.castSucc (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht B)
  have hm1 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc s.castSucc X.castSucc Y.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (under hm B)
  have hr1 : Derives Δ (ArgumentForestProgramSyntax.runs 2 w.castSucc R.castSucc S.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.runs_rename, SyntaxAtomSyntax.two_map]) (under hr B)
  have hFA1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) A.castSucc) := of_eq (by simp only [Formula.raise, SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hFA B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOut := at_forests hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc s.castSucc x.castSucc y.castSucc q.castSucc X.castSucc Y.castSucc A.castSucc (Fin.last m) hw1 hs1 ha1 ht1 hm1 hr1 hFA1 (.conjR hB)
  exact of_eq (OriginalFormulaMemberCaseSyntax.membershipCase_rename w mode depth parameter x y q Fin.castSucc).symm hOut

theorem from_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter R S c d s x y q X Y : Fin m)
    (hw : Derives Γ (omega w))
    (hs : Derives Γ (SyntaxAtomSyntax.zeroScalar w s))
    (ha : Derives Γ (MemberPairAgreementSyntax.agreement w mode depth parameter R S c d x y))
    (ht : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w c d (SyntaxAtomSyntax.two X Y)))
    (hm : Derives Γ (SyntaxAtomSyntax.memberCode w s X Y q))
    (hr : Derives Γ (ArgumentForestProgramSyntax.runs 2 w R S (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two X Y)))
    (hInputs : Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y))) :
    Derives Γ (OriginalFormulaMemberCaseSyntax.membershipCase w mode depth parameter x y q) := by
  let B := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) (Fin.last m))
  have he : Derives Γ (.ex B) := of_eq (by simp only [B, SyntaxForestSyntax.existsForest, SyntaxAtomSyntax.two_map]) (SyntaxForests.exists_forest hZ 2 w (SyntaxAtomSyntax.two x y) hw hInputs)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw B)
  have hs1 : Derives Δ (SyntaxAtomSyntax.zeroScalar w.castSucc s.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.zeroScalar_rename]) (under hs B)
  have ha1 : Derives Δ (MemberPairAgreementSyntax.agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc x.castSucc y.castSucc) := of_eq (by simp only [Formula.raise, MemberPairAgreementSyntax.agreement_rename]) (under ha B)
  have ht1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc c.castSucc d.castSucc (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under ht B)
  have hm1 : Derives Δ (SyntaxAtomSyntax.memberCode w.castSucc s.castSucc X.castSucc Y.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, SyntaxAtomSyntax.memberCode_rename]) (under hm B)
  have hr1 : Derives Δ (ArgumentForestProgramSyntax.runs 2 w.castSucc R.castSucc S.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) (SyntaxAtomSyntax.two X.castSucc Y.castSucc)) := of_eq (by simp only [Formula.raise, ArgumentForestProgramSyntax.runs_rename, SyntaxAtomSyntax.two_map]) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hOut := at_source_arguments hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc R.castSucc S.castSucc c.castSucc d.castSucc s.castSucc x.castSucc y.castSucc q.castSucc X.castSucc Y.castSucc (Fin.last m) hw1 hs1 ha1 ht1 hm1 hr1 (.conjR hB)
  exact of_eq (OriginalFormulaMemberCaseSyntax.membershipCase_rename w mode depth parameter x y q Fin.castSucc).symm hOut

end PPAC.Migration.Internal.MemberProgramIntro
