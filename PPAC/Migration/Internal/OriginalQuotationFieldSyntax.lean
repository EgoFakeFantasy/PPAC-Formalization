import PPAC.Migration.Internal.PureQuotationSyntax

/-! 原quotation子字段的有限纯合取；每个字段值仍为内部对象。 -/
namespace PPAC.Migration.Internal.OriginalQuotationFieldSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open OriginalTreeQuotationSyntax
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)

def fields {m} : (children : List Tree) → Fin m → (Fin children.length → Fin m) → Formula m
  | List.nil, w, _ => .equal w w
  | List.cons head tail, w, xs => (tree head w (xs 0)).conj (fields tail w (fun i => xs i.succ))

theorem fields_rename {m k} (children : List Tree) (w : Fin m) (xs : Fin children.length → Fin m) (ρ : Fin m → Fin k) :
    (fields children w xs).rename ρ = fields children (ρ w) (fun i => ρ (xs i)) := by
  induction children with
  | nil => rfl
  | cons head tail ih => simp only [fields, Formula.rename, tree_rename, ih]

theorem fields_at {m} {Γ : Context m} (children : List Tree) (w : Fin m) (xs : Fin children.length → Fin m)
    (i : Fin children.length) (hf : Derives Γ (fields children w xs)) : Derives Γ (tree (children.get i) w (xs i)) := by
  induction children with
  | nil => exact Fin.elim0 i
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .conjL hf
    · exact ih (fun k => xs k.succ) j (.conjR hf)

theorem intro_fields {m} {Γ : Context m} (children : List Tree) (w : Fin m) (xs : Fin children.length → Fin m)
    (hq : ∀ i, Derives Γ (tree (children.get i) w (xs i))) : Derives Γ (fields children w xs) := by
  induction children with
  | nil => exact .eqRefl w
  | cons head tail ih => exact .conjI (hq 0) (ih (fun k => xs k.succ) (fun i => hq i.succ))

theorem natural_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (children : List Tree) (w : Fin m)
    (xs : Fin children.length → Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (fields children w xs)) :
    Derives Γ (SyntaxForestSyntax.inputs children.length w xs) :=
  SyntaxForestSyntax.intro_inputs _ w xs (fun i => OriginalTreeQuotationProperties.tree_range hZ _ w (xs i) hw (fields_at children w xs i hf))

end PPAC.Migration.Internal.OriginalQuotationFieldSyntax
