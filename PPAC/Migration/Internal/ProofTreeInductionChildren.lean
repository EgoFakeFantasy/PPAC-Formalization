import PPAC.Migration.Internal.ProofTreeInductionSyntax

/-! 内部成员IH逐个作用于原child，原载荷字段严格下降提供成员前提。 -/
namespace PPAC.Migration.Internal.ProofTreeInductionChildren
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofTreeInductionSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

theorem ih_at {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (w code child : Fin m)
    (hi : Derives Γ (allIH test P w code)) (hm : Derives Γ (.mem child code))
    (hn : Derives Γ (ProofTreeEntrySyntax.node test w child)) : Derives Γ (property P w child) := by
  have hh : Derives Γ ((Formula.mem child code).imp (correct test P w child)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, correct_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE child hi)
  exact .impE (.impE hh hm) hn

theorem transfer_children {m a} {Γ : Context m} (test : Formula 1) (P : Formula 2) (is : List (Fin a))
    (w code : Fin m) (env : Fin a → Fin m) (hi : Derives Γ (allIH test P w code))
    (hb : ∀ i, i ∈ is → Derives Γ (.mem (env i) code))
    (hn : Derives Γ (ProofTreeChildren.children test is w env)) : Derives Γ (children P is w env) := by
  induction is with
  | nil => exact HornRuleSyntax.truth_proved
  | cons i is ih =>
    exact .conjI (ih_at test P w code (env i) hi (hb i List.mem_cons_self) (.conjL hn))
      (ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) (.conjR hn))

theorem payload_children {m} {Γ : Context m} (test : Formula 1) (P : Formula 2) (hZ : ZFContext.Evidence Γ)
    (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (allIH test P w code))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code))
    (hn : Derives Γ (ProofTreeChildren.children test (shape kind).children w env)) :
    Derives Γ (children P (shape kind).children w env) :=
  transfer_children test P (shape kind).children w code env hi
    (fun i _ => ProofTreeNodeSyntax.payload_field_below hZ kind w code env i hw hc) hn

end PPAC.Migration.Internal.ProofTreeInductionChildren
