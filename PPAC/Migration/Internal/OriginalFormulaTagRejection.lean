import PPAC.Migration.Internal.OriginalMemberRunDispatch

/-! 原十一分支的通用异标签排除；App 的实际标签2由内部载荷和数码单射确定。 -/
namespace PPAC.Migration.Internal.OriginalFormulaTagRejection
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem constant_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag k sourceTag : Nat) (hne : tag ≠ sourceTag)
     (w n q : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor k sourceTag w xs n))
    (he : Derives Γ (OriginalFormulaLocalData.constant tag w n q)) : Derives Γ .bot :=
  SyntaxConstructors.disjoint hZ 0 k tag sourceTag hne w Fin.elim0 xs n hw (.conjL he) hn

theorem binary_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind k sourceTag : Nat) (hne : tag ≠ sourceTag)
     (w mode depth parameter n q : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor k sourceTag w xs n))
    (he : Derives Γ (binaryCase tag kind w mode depth parameter n q)) : Derives Γ .bot := by
  let B := binaryBody tag kind w mode depth parameter n q
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ he
  have hZ1 := HornBinderRules.zf_body 4 hZ B
  have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw B)
  have hn1 : Derives Δ (SyntaxNodeSyntax.constructor k sourceTag (old 4 w) (fun i => old 4 (xs i)) (old 4 n)) := of_eq (SyntaxNodeSyntax.constructor_rename k sourceTag w xs n (old 4)) (HornBinderRules.under_body 4 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZ1 2 k tag sourceTag hne (old 4 w) (SyntaxAtomSyntax.two (slot 4 0) (slot 4 1)) (fun i => old 4 (xs i)) (old 4 n) hw1 (.conjL (.conjL hB)) hn1

theorem unary_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag k sourceTag : Nat) (hne : tag ≠ sourceTag)
     (w mode depth parameter n q : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor k sourceTag w xs n))
    (he : Derives Γ (unaryCase tag w mode depth parameter n q)) : Derives Γ .bot := by
  let B := unaryBody tag w mode depth parameter n q
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ he
  have hZ1 := HornBinderRules.zf_body 2 hZ B
  have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hn1 : Derives Δ (SyntaxNodeSyntax.constructor k sourceTag (old 2 w) (fun i => old 2 (xs i)) (old 2 n)) := of_eq (SyntaxNodeSyntax.constructor_rename k sourceTag w xs n (old 2)) (HornBinderRules.under_body 2 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact SyntaxConstructors.disjoint hZ1 1 k tag sourceTag hne (old 2 w) (fun _ => slot 2 0) (fun i => old 2 (xs i)) (old 2 n) hw1 (.conjL (.conjL hB)) hn1

theorem binder_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag k sourceTag : Nat) (hne : tag ≠ sourceTag)
     (w mode depth parameter n q : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor k sourceTag w xs n))
    (he : Derives Γ (binderCase tag w mode depth parameter n q)) : Derives Γ .bot := by
  let B := binderBody tag w mode depth parameter n q
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hn1 : Derives Δ (SyntaxNodeSyntax.constructor k sourceTag w.castSucc (fun i => (xs i).castSucc) n.castSucc) := of_eq (SyntaxNodeSyntax.constructor_rename k sourceTag w xs n Fin.castSucc) (under hn B)
  exact unary_rejected (ZFContext.under hZ B) tag k sourceTag hne w.castSucc mode.castSucc (Fin.last m) parameter.castSucc n.castSucc q.castSucc (fun i => (xs i).castSucc) hw1 hn1 (.conjR (.hyp (Or.inl rfl)))

theorem raw_application_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (k tag : Nat) (hne : tag ≠ 2) (w symbol args n : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n))
    (ha : Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n)) : Derives Γ .bot := by
  let B := OriginalFormulaApplicationSyntax.body w symbol args n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hZ1 : ZFContext.Evidence Δ := HornBinderRules.zf_body 3 hZ B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hn1 : Derives Δ (SyntaxNodeSyntax.constructor k tag (old 3 w) (fun i => old 3 (xs i)) (old 3 n)) := of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs n (old 3)) (HornBinderRules.under_body 3 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have htwo := SyntaxNumerals.range hZ1 2 (old 3 w) (slot 3 2) hw1 (.conjL (.conjR (.conjR hB)))
  have hp := StructuralConsCore.range hZ1 (old 3 w) (slot 3 0) (old 3 args) (slot 3 1) hw1 (.conjL (.conjR hB))
  let C := SyntaxNodeSyntax.constructorBody k tag (old 3 w) (fun i => old 3 (xs i)) (old 3 n)
  let Θ := Context.add C (Context.image Formula.raise Δ)
  apply SyntaxNodeSyntax.eliminate_constructor k tag (old 3 w) (fun i => old 3 (xs i)) (old 3 n) .bot hn1
  have hC : Derives Θ C := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 C
  have hw2 : Derives Θ (omega (old 3 w).castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 C)
  have ht : Derives Θ (SyntaxNumeralSyntax.numeral 2 (slot 3 2).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename 2 _ Fin.castSucc) (under (.conjL (.conjR (.conjR hB))) C)
  have hr : Derives Θ (StructuralNodeSyntax.raw (old 3 w).castSucc (slot 3 2).castSucc (slot 3 1).castSucc (old 3 n).castSucc) := of_eq (StructuralNodeSyntax.raw_rename _ _ _ _ Fin.castSucc) (under (.conjR (.conjR (.conjR hB))) C)
  have he := SyntaxNodeInjective.raw_tag_eq hZ2 k (old 3 w).castSucc (Fin.last (m+3)) (slot 3 2).castSucc (slot 3 1).castSucc (fun i => (old 3 (xs i)).castSucc) (old 3 n).castSucc hw2 (under htwo C) (under hp C) (.conjR hC) hr
  exact .impE (SyntaxNumerals.different hZ2 tag 2 hne _ _ (.conjL hC) ht) he

theorem application_rejected {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (k tag : Nat) (hne : tag ≠ 2) (w mode depth parameter n q : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n))
    (he : Derives Γ (applicationCase w mode depth parameter n q)) : Derives Γ .bot := by
  let B := applicationBody w mode depth parameter n q
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ he
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hn1 : Derives Δ (SyntaxNodeSyntax.constructor k tag (old 3 w) (fun i => old 3 (xs i)) (old 3 n)) := of_eq (SyntaxNodeSyntax.constructor_rename k tag w xs n (old 3)) (HornBinderRules.under_body 3 hn B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact raw_application_rejected (HornBinderRules.zf_body 3 hZ B) k tag hne (old 3 w) (slot 3 0) (slot 3 1) (old 3 n) (fun i => old 3 (xs i)) hw1 hn1 (.conjL (.conjL hB))

end PPAC.Migration.Internal.OriginalFormulaTagRejection
