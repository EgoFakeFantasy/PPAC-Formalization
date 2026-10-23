import PPAC.Migration.Internal.OriginalQuotationFormulaFields

/-! 任意纯内在公式的quotation在真实内部长度上下文中具有完整原FormulaCode类型。 -/
namespace PPAC.Migration.Internal.PureQuotationFormulaTyping
open Source SourceAlgebra SourceLogic OmegaSyntax PureQuotationTypedSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem formula_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral bound.length b)) (hf : Derives Γ (SyntaxNumeralSyntax.numeral free.length f))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  induction input generalizing m with
  | @falsum bound free =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    exact OriginalQuotationFormulaFields.nullary_type hZ false w b f n hw hCtx hn
  | @truth bound free =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    exact OriginalQuotationFormulaFields.nullary_type hZ true w b f n hw hCtx hn
  | @equal bound free sort left right =>
    cases sort
    have he1 := PureQuotationTypedTerms.exists_typed hZ left w b f hw hb hf
    let X := termValue left w.castSucc b.castSucc f.castSucc (Fin.last m)
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.equal left right) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.equal left right) w n Fin.castSucc) (under hn X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have he2 := PureQuotationTypedTerms.exists_typed hZ1 right w.castSucc b.castSucc f.castSucc hw1 hb1 hf1
    let Y := termValue right w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) he2
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Y)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 Y)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.equal left right) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.equal left right) w.castSucc n.castSucc Fin.castSucc) (under hn1 Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hX2 : Derives Ξ (termValue left w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [X, Formula.raise, termValue_rename]) (under hX Y)
    have ho := OriginalQuotationFormulaFields.equal_type hZ2 (PureSyntaxQuotation.termTree left) (PureSyntaxQuotation.termTree right) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hn2 (.conjL hX2) (.conjL hY) (.conjR hX2) (.conjR hY)
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @rel bound free symbol args =>
    cases symbol
    match args with
    | .cons left (.cons right .nil) =>
      have he1 := OriginalTreeQuotationExistence.tree_exists hZ (leaf 0) w hw
      let S := (Formula.mem (Fin.last m) w.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc (Fin.last m))
      let Δ := Context.add S (Context.image Formula.raise Γ)
      apply Derives.exE (p := S) he1
      have hZ1 := ZFContext.under hZ S
      have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw S)
      have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb S)
      have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf S)
      have hn1 : Derives Δ (PureQuotationSyntax.formula (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w n Fin.castSucc) (under hn S)
      have hS : Derives Δ S := .hyp (Or.inl rfl)
      have he2 := PureQuotationTypedTerms.exists_typed hZ1 left w.castSucc b.castSucc f.castSucc hw1 hb1 hf1
      let X := termValue left w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
      let Ξ := Context.add X (Context.image Formula.raise Δ)
      apply Derives.exE (p := X) he2
      have hZ2 := ZFContext.under hZ1 X
      have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 X)
      have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 X)
      have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 X)
      have hn2 : Derives Ξ (PureQuotationSyntax.formula (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w.castSucc n.castSucc Fin.castSucc) (under hn1 X)
      have hX : Derives Ξ X := .hyp (Or.inl rfl)
      have hS2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [S, Formula.raise, Formula.rename, OriginalTreeQuotationSyntax.tree_rename]) (under hS X)
      have he3 := PureQuotationTypedTerms.exists_typed hZ2 right w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc hw2 hb2 hf2
      let Y := termValue right w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last (m+2))
      let Ω := Context.add Y (Context.image Formula.raise Ξ)
      apply Derives.exE (p := Y) he3
      have hZ3 := ZFContext.under hZ2 Y
      have hw3 : Derives Ω (omega w.castSucc.castSucc.castSucc) := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 Y)
      have hb3 : Derives Ω (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc.castSucc Fin.castSucc) (under hb2 Y)
      have hf3 : Derives Ω (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc.castSucc Fin.castSucc) (under hf2 Y)
      have hn3 : Derives Ω (PureQuotationSyntax.formula (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.rel YesMetaZFC.SetTheory.RelationSymbol.membership (.cons left (.cons right .nil))) w.castSucc.castSucc n.castSucc.castSucc Fin.castSucc) (under hn2 Y)
      have hY : Derives Ω Y := .hyp (Or.inl rfl)
      have hS3 : Derives Ω ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, Formula.rename, OriginalTreeQuotationSyntax.tree_rename]) (under hS2 Y)
      have hX3 : Derives Ω (termValue left w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) := of_eq (by simp only [X, Formula.raise, termValue_rename]) (under hX Y)
      have ho := OriginalQuotationFormulaFields.member_type hZ3 (PureSyntaxQuotation.termTree left) (PureSyntaxQuotation.termTree right) w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 hn3 (.conjR hS3) (.conjL hX3) (.conjL hY) (.conjR hX3) (.conjR hY)
      exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @neg bound free body ih =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree body) w hw
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula body w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.neg body) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.neg body) w n Fin.castSucc) (under hn X)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have ht := ih hZ1 w.castSucc b.castSucc f.castSucc (Fin.last m) hw1 hb1 hf1 (.conjR hX)
    have ho := OriginalQuotationFormulaFields.negation_type hZ1 (PureSyntaxQuotation.formulaTree body) w.castSucc b.castSucc f.castSucc n.castSucc (Fin.last m) hw1 hCtx1 hn1 (.conjR hX) ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @conj bound free left right ihL ihR =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree left) w hw
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula left w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.conj left right) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.conj left right) w n Fin.castSucc) (under hn X)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree right) w.castSucc hw1
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula right w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) he2
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Y)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 Y)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.conj left right) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.conj left right) w.castSucc n.castSucc Fin.castSucc) (under hn1 Y)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (PureQuotationSyntax.formula left w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [X, Formula.raise, Formula.rename, PureQuotationSyntax.formula_rename]) (under hX Y)
    have htX := ihL hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc hw2 hb2 hf2 (.conjR hX2)
    have htY := ihR hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hf2 (.conjR hY)
    have ho := OriginalQuotationFormulaFields.binary_type hZ2 0 (PureSyntaxQuotation.formulaTree left) (PureSyntaxQuotation.formulaTree right) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hCtx2 hn2 (.conjR hX2) (.conjR hY) htX htY
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @disj bound free left right ihL ihR =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree left) w hw
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula left w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.disj left right) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.disj left right) w n Fin.castSucc) (under hn X)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree right) w.castSucc hw1
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula right w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) he2
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Y)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 Y)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.disj left right) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.disj left right) w.castSucc n.castSucc Fin.castSucc) (under hn1 Y)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (PureQuotationSyntax.formula left w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [X, Formula.raise, Formula.rename, PureQuotationSyntax.formula_rename]) (under hX Y)
    have htX := ihL hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc hw2 hb2 hf2 (.conjR hX2)
    have htY := ihR hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hf2 (.conjR hY)
    have ho := OriginalQuotationFormulaFields.binary_type hZ2 1 (PureSyntaxQuotation.formulaTree left) (PureSyntaxQuotation.formulaTree right) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hCtx2 hn2 (.conjR hX2) (.conjR hY) htX htY
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @imp bound free left right ihL ihR =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree left) w hw
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula left w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.imp left right) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.imp left right) w n Fin.castSucc) (under hn X)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree right) w.castSucc hw1
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula right w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) he2
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Y)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 Y)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.imp left right) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.imp left right) w.castSucc n.castSucc Fin.castSucc) (under hn1 Y)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (PureQuotationSyntax.formula left w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [X, Formula.raise, Formula.rename, PureQuotationSyntax.formula_rename]) (under hX Y)
    have htX := ihL hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc hw2 hb2 hf2 (.conjR hX2)
    have htY := ihR hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hf2 (.conjR hY)
    have ho := OriginalQuotationFormulaFields.binary_type hZ2 2 (PureSyntaxQuotation.formulaTree left) (PureSyntaxQuotation.formulaTree right) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hCtx2 hn2 (.conjR hX2) (.conjR hY) htX htY
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @iff bound free left right ihL ihR =>
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree left) w hw
    let X := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula left w.castSucc (Fin.last m))
    let Δ := Context.add X (Context.image Formula.raise Γ)
    apply Derives.exE (p := X) he1
    have hZ1 := ZFContext.under hZ X
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw X)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb X)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf X)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.iff left right) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.iff left right) w n Fin.castSucc) (under hn X)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx X)
    have hX : Derives Δ X := .hyp (Or.inl rfl)
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree right) w.castSucc hw1
    let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula right w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add Y (Context.image Formula.raise Δ)
    apply Derives.exE (p := Y) he2
    have hZ2 := ZFContext.under hZ1 Y
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Y)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 Y)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 Y)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.iff left right) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.iff left right) w.castSucc n.castSucc Fin.castSucc) (under hn1 Y)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 Y)
    have hY : Derives Ξ Y := .hyp (Or.inl rfl)
    have hX2 : Derives Ξ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (PureQuotationSyntax.formula left w.castSucc.castSucc (Fin.last m).castSucc)) := of_eq (by simp only [X, Formula.raise, Formula.rename, PureQuotationSyntax.formula_rename]) (under hX Y)
    have htX := ihL hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc hw2 hb2 hf2 (.conjR hX2)
    have htY := ihR hZ2 w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hb2 hf2 (.conjR hY)
    have ho := OriginalQuotationFormulaFields.binary_type hZ2 3 (PureSyntaxQuotation.formulaTree left) (PureSyntaxQuotation.formulaTree right) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hCtx2 hn2 (.conjR hX2) (.conjR hY) htX htY
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @forallE bound free sort body ih =>
    cases sort
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := InsertExistence.exists_insert b b (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
    let K := successor (Fin.last m) b.castSucc
    let Δ := Context.add K (Context.image Formula.raise Γ)
    apply Derives.exE (p := K) he1
    have hZ1 := ZFContext.under hZ K
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw K)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb K)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf K)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.forallE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.forallE YesMetaZFC.SetTheory.SetSort.set body) w n Fin.castSucc) (under hn K)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx K)
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have hbK := SyntaxNumeralSyntax.intro_succ bound.length (Fin.last m) b.castSucc hb1 hK
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree body) w.castSucc hw1
    let X := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula body w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add X (Context.image Formula.raise Δ)
    apply Derives.exE (p := X) he2
    have hZ2 := ZFContext.under hZ1 X
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 X)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 X)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 X)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.forallE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.forallE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc n.castSucc Fin.castSucc) (under hn1 X)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 X)
    have hX : Derives Ξ X := .hyp (Or.inl rfl)
    have hbK2 : Derives Ξ (SyntaxNumeralSyntax.numeral (bound.length+1) (Fin.last m).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ (Fin.last m) Fin.castSucc) (under hbK X)
    have hK2 : Derives Ξ (successor (Fin.last m).castSucc b.castSucc.castSucc) := of_eq (by simp only [K, Formula.raise, successor_rename]) (under hK X)
    have ht := ih hZ2 w.castSucc.castSucc (Fin.last m).castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hbK2 hf2 (.conjR hX)
    have ho := OriginalQuotationFormulaFields.quantified_type hZ2 true (PureSyntaxQuotation.formulaTree body) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 hCtx2 hn2 (.conjR hX) hK2 ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho
  | @existsE bound free sort body ih =>
    cases sort
    have hCtx := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w b f hw hb hf
    have he1 := InsertExistence.exists_insert b b (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
    let K := successor (Fin.last m) b.castSucc
    let Δ := Context.add K (Context.image Formula.raise Γ)
    apply Derives.exE (p := K) he1
    have hZ1 := ZFContext.under hZ K
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw K)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length b.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b Fin.castSucc) (under hb K)
    have hf1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length f.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f Fin.castSucc) (under hf K)
    have hn1 : Derives Δ (PureQuotationSyntax.formula (.existsE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc n.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.existsE YesMetaZFC.SetTheory.SetSort.set body) w n Fin.castSucc) (under hn K)
    have hCtx1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc b.castSucc f.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w b f Fin.castSucc) (under hCtx K)
    have hK : Derives Δ K := .hyp (Or.inl rfl)
    have hbK := SyntaxNumeralSyntax.intro_succ bound.length (Fin.last m) b.castSucc hb1 hK
    have he2 := OriginalTreeQuotationExistence.tree_exists hZ1 (PureSyntaxQuotation.formulaTree body) w.castSucc hw1
    let X := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (PureQuotationSyntax.formula body w.castSucc.castSucc (Fin.last (m+1)))
    let Ξ := Context.add X (Context.image Formula.raise Δ)
    apply Derives.exE (p := X) he2
    have hZ2 := ZFContext.under hZ1 X
    have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 X)
    have hb2 : Derives Ξ (SyntaxNumeralSyntax.numeral bound.length b.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ b.castSucc Fin.castSucc) (under hb1 X)
    have hf2 : Derives Ξ (SyntaxNumeralSyntax.numeral free.length f.castSucc.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ f.castSucc Fin.castSucc) (under hf1 X)
    have hn2 : Derives Ξ (PureQuotationSyntax.formula (.existsE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc.castSucc n.castSucc.castSucc) := of_eq (PureQuotationSyntax.formula_rename (.existsE YesMetaZFC.SetTheory.SetSort.set body) w.castSucc n.castSucc Fin.castSucc) (under hn1 X)
    have hCtx2 : Derives Ξ (SyntaxTermSyntax.contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := of_eq (SyntaxTermSyntax.contexts_rename w.castSucc b.castSucc f.castSucc Fin.castSucc) (under hCtx1 X)
    have hX : Derives Ξ X := .hyp (Or.inl rfl)
    have hbK2 : Derives Ξ (SyntaxNumeralSyntax.numeral (bound.length+1) (Fin.last m).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ (Fin.last m) Fin.castSucc) (under hbK X)
    have hK2 : Derives Ξ (successor (Fin.last m).castSucc b.castSucc.castSucc) := of_eq (by simp only [K, Formula.raise, successor_rename]) (under hK X)
    have ht := ih hZ2 w.castSucc.castSucc (Fin.last m).castSucc f.castSucc.castSucc (Fin.last (m+1)) hw2 hbK2 hf2 (.conjR hX)
    have ho := OriginalQuotationFormulaFields.quantified_type hZ2 false (PureSyntaxQuotation.formulaTree body) w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc hw2 hCtx2 hn2 (.conjR hX) hK2 ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) ho

end PPAC.Migration.Internal.PureQuotationFormulaTyping
