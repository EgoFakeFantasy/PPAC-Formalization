import PPAC.Migration.Internal.OriginalArgumentsTraceEquation

/-! 原五字段根行实际存在及两分支的自然输入/输出，消去预给行码所需的对象见证。 -/
namespace PPAC.Migration.Internal.OriginalArgumentRoots
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalArgumentCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Nat)
    (w mode depth parameter input output : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (.mem mode w)) (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (.mem input w)) (hq : Derives Γ (.mem output w)) :
    Derives Γ (.ex ((Formula.mem (Fin.last m) w.castSucc).conj
      (OriginalTransformRowSyntax.row kind w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)))) := by
  have hs : ∀ i, Derives Γ (.mem (HornRowFields.five mode depth parameter input output i) w) := by
    intro i
    exact Fin.cases hm (fun a => Fin.cases hd (fun b => Fin.cases hp (fun c => Fin.cases hn (fun _ => hq) c) b) a) i
  have he := SyntaxConstructors.exists_constructor hZ 5 kind w (HornRowFields.five mode depth parameter input output) hw (SyntaxForestSyntax.intro_inputs 5 _ _ hs)
  exact of_eq (by simp only [SyntaxNodeSyntax.existsConstructor, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map]) he

theorem outcomes_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter input output : Fin m) (hw : Derives Γ (omega w))
    (ho : Derives Γ (outcomes w mode depth parameter input output)) :
    Derives Γ ((Formula.mem input w).conj (.mem output w)) := by
  apply Derives.disjE ho
  · let E := nilData w input output
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact .conjI (StructuralNil.range (ZFContext.add hZ E) w input (add hw E) (.conjL hE))
      (StructuralNil.range (ZFContext.add hZ E) w output (add hw E) (.conjR hE))
  · let E := consCase w mode depth parameter input output
    let B := consBody w mode depth parameter input output
    let Δ := Context.add B (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) B
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact .conjI (StructuralConsCore.range hZ1 _ _ _ _ hw1 (.conjL (.conjL hB)))
      (StructuralConsCore.range hZ1 _ _ _ _ hw1 (.conjR (.conjL hB)))

end PPAC.Migration.Internal.OriginalArgumentRoots
