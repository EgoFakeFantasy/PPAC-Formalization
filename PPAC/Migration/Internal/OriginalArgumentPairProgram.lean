import PPAC.Migration.Internal.ArgumentPairProgramFields

/-! 原mode0／3的两参数Run₂在全部内部输出候选上的独立项程序精确双条件。 -/
namespace PPAC.Migration.Internal.OriginalArgumentPairProgram
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem at_length_replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y len : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (hLen : Derives Γ (SyntaxNumeralSyntax.numeral 2 len)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff (ArgumentPairProgramSyntax.returned w R L a c x y q)) := by
  have hList := ArgumentForestTyping.list_of_forest hZ 2 w len a b n (SyntaxAtomSyntax.two x y) h0 hLen (.conjL (.conjL hT)) hN hT
  have hOriginal := OriginalArgumentFullProgramBridge.replace_iff hZ w mode depth a b c L I R n q len h0 h1 h2 h3 h4 h5 hList
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal (ArgumentPairProgramFields.mapped_iff hZ w R L len a c n q x y h0 hLen hN)

theorem replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth L n q).iff (ArgumentPairProgramSyntax.returned w R L a c x y q)) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxNumerals.exists_numeral hZ 2 w h0)
  have hZ1 := ZFContext.under hZ E
  have h01 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under h0 E)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 3 mode Fin.castSucc) (under h1 E)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc L.castSucc) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth L Fin.castSucc) (under h2 E)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I Fin.castSucc) (under h3 E)
  have h41 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc c.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a c Fin.castSucc) (under h4 E)
  have h51 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termList_rename w b a c L Fin.castSucc) (under h5 E)
  have hN1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) n.castSucc) := of_eq (by simp only [SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hN E)
  have hT1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc a.castSucc b.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under hT E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_length_replace_iff hZ1 w.castSucc mode.castSucc depth.castSucc a.castSucc b.castSucc c.castSucc L.castSucc I.castSucc R.castSucc n.castSucc q.castSucc x.castSucc y.castSucc (Fin.last m) h01 h11 h21 h31 h41 h51 hN1 hT1 (.conjR hE)
  simpa only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, ArgumentPairProgramSyntax.returned_rename] using ho

theorem at_length_weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y len : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y)))
    (hLen : Derives Γ (SyntaxNumeralSyntax.numeral 2 len)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (ArgumentPairProgramSyntax.returned w R S a B x y q)) := by
  have hList := ArgumentForestTyping.list_of_forest hZ 2 w len a b n (SyntaxAtomSyntax.two x y) h0 hLen (.conjL (.conjL hT)) hN hT
  have hOriginal := OriginalArgumentFullProgramBridge.weaken_iff hZ w mode depth parameter a b B I J R S n q len h0 h1 h2 h3 h4 h5 h6 hList
  exact SyntaxTypeLocalTransfer.iff_trans hOriginal (ArgumentPairProgramFields.mapped_iff hZ w R S len a B n q x y h0 hLen hN)

theorem weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q x y : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hN : Derives Γ (SyntaxForestSyntax.forest 2 w (SyntaxAtomSyntax.two x y) n))
    (hT : Derives Γ (ArgumentForestProgramSyntax.typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n q).iff (ArgumentPairProgramSyntax.returned w R S a B x y q)) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNumeralSyntax.numeral 2 (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxNumerals.exists_numeral hZ 2 w h0)
  have hZ1 := ZFContext.under hZ E
  have h01 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under h0 E)
  have h11 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 0 mode Fin.castSucc) (under h1 E)
  have h21 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc depth.castSucc parameter.castSucc) := of_eq (OriginalTermTraceSyntax.metadata_rename w depth parameter Fin.castSucc) (under h2 E)
  have h31 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc I.castSucc) := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I Fin.castSucc) (under h3 E)
  have h41 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w.castSucc b.castSucc B.castSucc J.castSucc) := of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w b B J Fin.castSucc) (under h4 E)
  have h51 : Derives Δ (IndexTermImageCodeSyntax.converted true w.castSucc I.castSucc R.castSucc a.castSucc a.castSucc B.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename true w I R a a B Fin.castSucc) (under h5 E)
  have h61 : Derives Δ (IndexTermImageCodeSyntax.converted false w.castSucc J.castSucc S.castSucc b.castSucc a.castSucc B.castSucc) := of_eq (IndexTermImageCodeSyntax.converted_rename false w J S b a B Fin.castSucc) (under h6 E)
  have hN1 : Derives Δ (SyntaxForestSyntax.forest 2 w.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc) n.castSucc) := of_eq (by simp only [SyntaxForestSyntax.forest_rename, SyntaxAtomSyntax.two_map]) (under hN E)
  have hT1 : Derives Δ (ArgumentForestProgramSyntax.typedInputs 2 w.castSucc a.castSucc b.castSucc (SyntaxAtomSyntax.two x.castSucc y.castSucc)) := of_eq (by simp only [ArgumentForestProgramSyntax.typedInputs_rename, SyntaxAtomSyntax.two_map]) (under hT E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_length_weaken_iff hZ1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc B.castSucc I.castSucc J.castSucc R.castSucc S.castSucc n.castSucc q.castSucc x.castSucc y.castSucc (Fin.last m) h01 h11 h21 h31 h41 h51 h61 hN1 hT1 (.conjR hE)
  simpa only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, ArgumentPairProgramSyntax.returned_rename] using ho

end PPAC.Migration.Internal.OriginalArgumentPairProgram
