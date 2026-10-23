import PPAC.Migration.Internal.AtomicProgramMerge

/-! 全部内部原子输入上的原mode0／3整条Run₃与实际四分支原子程序双向对应。 -/
namespace PPAC.Migration.Internal.OriginalAtomicProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem replace_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaAtomicProgramSyntax.run w R L a b a c n q)) := by
  have ht : Derives Γ (SyntaxTermSyntax.contexts w a c) := .conjL (.conjR h5)
  have hfalse : Derives Γ ((SyntaxAtomSyntax.nullary false w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.nullary false w a b a c n q))) := .impI (OriginalAtomicExistingAtom.constant_iff (ZFContext.add hZ _) true false w mode depth L a b a c n q (add h0 _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl)) (add ht _))
  have htrue : Derives Γ ((SyntaxAtomSyntax.nullary true w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.nullary true w a b a c n q))) := .impI (OriginalAtomicExistingAtom.constant_iff (ZFContext.add hZ _) true true w mode depth L a b a c n q (add h0 _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl)) (add ht _))
  have hmembership : Derives Γ ((SyntaxAtomSyntax.membership w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.membership w R L a b a c n q))) := .impI (OriginalTypedAtomicCases.replace_membership_iff (ZFContext.add hZ _) w mode depth a b c L I R n q (add h0 _) (add h1 _) (add h2 _) (add h3 _) (add h4 _) (add h5 _) (.hyp (Or.inl rfl)))
  have hequality : Derives Γ ((SyntaxAtomSyntax.equality w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformAtomSyntax.equality w R L a b a c n q))) := .impI (OriginalTypedAtomicCases.replace_equality_iff (ZFContext.add hZ _) w mode depth a b c L I R n q (add h0 _) (add h1 _) (add h2 _) (add h3 _) (add h4 _) (add h5 _) (.hyp (Or.inl rfl)))
  exact AtomicProgramMerge.merge (OriginalTransformRowSyntax.run 3 w mode depth L n q) w R L a b a c n q hfalse htrue hmembership hequality hA

theorem weaken_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaAtomicProgramSyntax.run w R S a b a B n q)) := by
  have ht : Derives Γ (SyntaxTermSyntax.contexts w a B) := .conjL (.conjR (IndexTermImageCodeTyping.term_list true w I R a a B h5))
  have hfalse : Derives Γ ((SyntaxAtomSyntax.nullary false w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.nullary false w a b a B n q))) := .impI (OriginalAtomicExistingAtom.constant_iff (ZFContext.add hZ _) false false w mode depth parameter a b a B n q (add h0 _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl)) (add ht _))
  have htrue : Derives Γ ((SyntaxAtomSyntax.nullary true w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.nullary true w a b a B n q))) := .impI (OriginalAtomicExistingAtom.constant_iff (ZFContext.add hZ _) false true w mode depth parameter a b a B n q (add h0 _) (add h1 _) (add h2 _) (.hyp (Or.inl rfl)) (add ht _))
  have hmembership : Derives Γ ((SyntaxAtomSyntax.membership w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.membership w R S a b a B n q))) := .impI (OriginalTypedAtomicCases.weaken_membership_iff (ZFContext.add hZ _) w mode depth parameter a b B I J R S n q (add h0 _) (add h1 _) (add h2 _) (add h3 _) (add h4 _) (add h5 _) (add h6 _) (.hyp (Or.inl rfl)))
  have hequality : Derives Γ ((SyntaxAtomSyntax.equality w a b n).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformAtomSyntax.equality w R S a b a B n q))) := .impI (OriginalTypedAtomicCases.weaken_equality_iff (ZFContext.add hZ _) w mode depth parameter a b B I J R S n q (add h0 _) (add h1 _) (add h2 _) (add h3 _) (add h4 _) (add h5 _) (add h6 _) (.hyp (Or.inl rfl)))
  exact AtomicProgramMerge.merge (OriginalTransformRowSyntax.run 3 w mode depth parameter n q) w R S a b a B n q hfalse htrue hmembership hequality hA

theorem replace_program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth a b c L I R h n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 3 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth L))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a c))
    (h5 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w b a c L))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth L n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R L a b a c h n q)) :=
  SyntaxRenameQuerySyntax.of_eq (congrArg (fun r => (OriginalTransformRowSyntax.run 3 w mode depth L n q).iff r) (FormulaAtomicProgramSyntax.run_eq_program w R L a b a c h n q))
    (replace_iff hZ w mode depth a b c L I R n q h0 h1 h2 h3 h4 h5 hA)

theorem weaken_program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter a b B I J R S h n q : Fin m)
    (h0 : Derives Γ (omega w))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (h2 : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (h3 : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (h4 : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (h5 : Derives Γ (IndexTermImageCodeSyntax.converted true w I R a a B))
    (h6 : Derives Γ (IndexTermImageCodeSyntax.converted false w J S b a B))
    (hA : Derives Γ (SyntaxAtomSyntax.atomic w a b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b a B h n q)) :=
  SyntaxRenameQuerySyntax.of_eq (congrArg (fun r => (OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff r) (FormulaAtomicProgramSyntax.run_eq_program w R S a b a B h n q))
    (weaken_iff hZ w mode depth parameter a b B I J R S n q h0 h1 h2 h3 h4 h5 h6 hA)
end PPAC.Migration.Internal.OriginalAtomicProgram
