import PPAC.Migration.Internal.ObjectOriginalArgumentPair

/-! 独立纯成员项程序分支：实际输出两个项由对象量词绑定，不调用原公式运行。 -/
namespace PPAC.Migration.Internal.MemberProgramSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax ArgumentForestProgramSyntax
open SyntaxRenameQuerySyntax (of_eq)

def body {m} (w R S c d s x y q : Fin m) : Formula (m+2) :=
  (typedInputs 2 (old 2 w) (old 2 c) (old 2 d) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))).conj
    ((SyntaxAtomSyntax.memberCode (old 2 w) (old 2 s) (slot 2 0) (slot 2 1) (old 2 q)).conj
      (runs 2 (old 2 w) (old 2 R) (old 2 S) (SyntaxAtomSyntax.two (old 2 x) (old 2 y)) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))))

def returned {m} (w R S c d s x y q : Fin m) : Formula m := existsMany 2 (body w R S c d s x y q)

theorem body_lift {m j} (w R S c d s x y q : Fin m) (ρ : Fin m → Fin j) :
    (body w R S c d s x y q).rename (lift 2 ρ) = body (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ s) (ρ x) (ρ y) (ρ q) := by
  simp only [body, Formula.rename, typedInputs_rename, SyntaxAtomSyntax.memberCode_rename, runs_rename, SyntaxAtomSyntax.two_map, lift_old, lift_slot]

theorem returned_rename {m j} (w R S c d s x y q : Fin m) (ρ : Fin m → Fin j) :
    (returned w R S c d s x y q).rename ρ = returned (ρ w) (ρ R) (ρ S) (ρ c) (ρ d) (ρ s) (ρ x) (ρ y) (ρ q) := by
  simp only [returned, existsMany_rename, body_lift]

theorem intro_returned {m} {Γ : Context m} (w R S c d s x y q X Y : Fin m)
    (ht : Derives Γ (typedInputs 2 w c d (SyntaxAtomSyntax.two X Y)))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w s X Y q))
    (hr : Derives Γ (runs 2 w R S (SyntaxAtomSyntax.two x y) (SyntaxAtomSyntax.two X Y))) :
    Derives Γ (returned w R S c d s x y q) := by
  apply HornBinderRules.intro_many 2 (body w R S c d s x y q) (SyntaxAtomSyntax.two X Y)
  exact of_eq (by simp only [body, Formula.rename, typedInputs_rename, SyntaxAtomSyntax.memberCode_rename, runs_rename, SyntaxAtomSyntax.two_map, assign_old, assign_slot]; rfl) (.conjI ht (.conjI hc hr))

theorem inputs_from_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b x y : Fin m)
    (hw : Derives Γ (OmegaSyntax.omega w))
    (ht : Derives Γ (typedInputs 2 w a b (SyntaxAtomSyntax.two x y))) :
    Derives Γ (SyntaxForestSyntax.inputs 2 w (SyntaxAtomSyntax.two x y)) :=
  SyntaxForestSyntax.intro_inputs 2 w (SyntaxAtomSyntax.two x y)
    (fun i => SyntaxTerms.range hZ w a b _ hw (typed_at 2 w a b _ ht i))

end PPAC.Migration.Internal.MemberProgramSyntax
