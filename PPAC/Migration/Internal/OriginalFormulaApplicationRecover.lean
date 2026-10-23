import PPAC.Migration.Internal.OriginalFormulaApplicationNodes

/-! 在实际首字段节点处反向恢复原App的符号树码与整个参数森林。 -/
namespace PPAC.Migration.Internal.OriginalFormulaApplicationRecover
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxNodeSyntax SyntaxForestSyntax OriginalFormulaApplicationNodes

theorem recover_at_node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w s args a payload two tag n : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hargs : Derives Γ (.mem args w))
    (htwo : Derives Γ (.mem two w)) (hc : Derives Γ (StructuralListSyntax.consCode w a args payload))
    (hr : Derives Γ (StructuralNodeSyntax.raw w two payload n))
    (hn : Derives Γ (node (k+1) w tag (prepend k s xs) n)) :
    Derives Γ ((Formula.equal a s).conj (forest k w xs args)) := by
  let N := nodeBody (k+1) w tag (prepend k s xs) n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node (k+1) w tag (prepend k s xs) n _ hn
  have hZ1 := ZFContext.under hZ N
  have lift1 {p : Formula m} (h : Derives Γ p) : Derives Ξ p.raise := under h N
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (lift1 hw)
  have hc1 : Derives Ξ (StructuralListSyntax.consCode w.castSucc a.castSucc args.castSucc payload.castSucc) := of_eq (StructuralListSyntax.consCode_rename w a args payload Fin.castSucc) (lift1 hc)
  have hr1 : Derives Ξ (StructuralNodeSyntax.raw w.castSucc two.castSucc payload.castSucc n.castSucc) := of_eq (StructuralNodeSyntax.raw_rename w two payload n Fin.castSucc) (lift1 hr)
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hPayload := SyntaxForests.range hZ1 (k+1) _ _ _ hw1 (.conjL (.conjR hN))
  have hEq := StructuralNodeCore.injective hZ1 _ _ _ _ _ _ hw1 (.conjL hN) hPayload (lift1 htwo) (StructuralConsCore.range hZ1 _ _ _ _ hw1 hc1) (.conjR (.conjR hN)) hr1
  have hForest := SyntaxForestInjective.output_subst (k+1) _ _ _ _ (.conjR hEq) (.conjL (.conjR hN))
  let C := (Formula.mem s.castSucc.castSucc w.castSucc.castSucc).conj
    ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).conj
      (StructuralListSyntax.consCode w.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) payload.castSucc.castSucc))
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) hForest
  have hZ2 := ZFContext.under hZ1 C
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := under (under h N) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hc2 : Derives Δ (StructuralListSyntax.consCode w.castSucc.castSucc a.castSucc.castSucc args.castSucc.castSucc payload.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (lift hc)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := StructuralConsUnique.injective hZ2 _ _ _ _ _ _ hw2 (lift ha) (lift hargs) (.conjL hC) (SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hC))) hc2 (.conjR (.conjR hC))
  have ho := Derives.conjI (.conjL he) (SyntaxForestInjective.output_subst k _ _ _ _ (eq_symm (.conjR he)) (.conjL (.conjR hC)))
  simpa only [Formula.raise, Formula.rename, forest_rename] using ho

theorem recover_at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w s args a payload two n : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hargs : Derives Γ (.mem args w))
    (htwo : Derives Γ (.mem two w)) (hc : Derives Γ (StructuralListSyntax.consCode w a args payload))
    (hr : Derives Γ (StructuralNodeSyntax.raw w two payload n))
    (hn : Derives Γ (constructor (k+1) 2 w (prepend k s xs) n)) :
    Derives Γ ((Formula.equal a s).conj (forest k w xs args)) := by
  let B := constructorBody (k+1) 2 w (prepend k s xs) n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_constructor (k+1) 2 w (prepend k s xs) n _ hn
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (StructuralListSyntax.consCode w.castSucc a.castSucc args.castSucc payload.castSucc) := of_eq (StructuralListSyntax.consCode_rename w a args payload Fin.castSucc) (under hc B)
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc two.castSucc payload.castSucc n.castSucc) := of_eq (StructuralNodeSyntax.raw_rename w two payload n Fin.castSucc) (under hr B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := recover_at_node hZ1 k w.castSucc s.castSucc args.castSucc a.castSucc payload.castSucc two.castSucc (Fin.last m) n.castSucc (fun i => (xs i).castSucc) hw1 (under ha B) (under hargs B) (under htwo B) hc1 hr1 (.conjR hB)
  simpa only [Formula.raise, Formula.rename, forest_rename] using ho

theorem recover_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w symbol s args n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hargs : Derives Γ (.mem args w)) (hn : Derives Γ (constructor (k+1) 2 w (prepend k s xs) n))
    (ha : Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n)) :
    Derives Γ ((scalar w symbol s).conj (forest k w xs args)) := by
  let B := OriginalFormulaApplicationSyntax.body w symbol args n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 h B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
  have hn1 : Derives Δ (constructor (k+1) 2 (old 3 w) (prepend k (old 3 s) (fun i => old 3 (xs i))) (old 3 n)) := of_eq (by simp only [constructor_rename, prepend_map]) (lift hn)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ht := SyntaxNumerals.range hZ1 2 _ _ hw1 (.conjL (.conjR (.conjR hB)))
  have he := recover_at_constructor hZ1 k (old 3 w) (old 3 s) (old 3 args) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 n) (fun i => old 3 (xs i)) hw1 (SyntaxNodes.range hZ1 0 _ _ _ _ hw1 (.conjL hB)) (lift hargs) ht (.conjL (.conjR hB)) (.conjR (.conjR (.conjR hB))) hn1
  have hs := SyntaxNodeInjective.scalar_output_subst _ _ _ _ (.conjL he) (.conjL hB)
  exact of_eq (by simp only [Formula.rename, scalar_rename, forest_rename]) (.conjI hs (.conjR he))

end PPAC.Migration.Internal.OriginalFormulaApplicationRecover
