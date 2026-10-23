import PPAC.Migration.Internal.ObjectOriginalFormulaEquation
import PPAC.Migration.Internal.StructuralListCodeFields

/-! 原App与首字段符号树码／实际参数森林的节点对应；所有见证留在对象量词中。 -/
namespace PPAC.Migration.Internal.OriginalFormulaApplicationNodes
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxNodeSyntax SyntaxForestSyntax

def prepend {m} (k : Nat) (s : Fin m) (xs : Fin k → Fin m) : Fin (k+1) → Fin m := Fin.cases s xs

theorem prepend_zero {m} (k : Nat) (s : Fin m) (xs : Fin k → Fin m) : prepend k s xs 0 = s := rfl

theorem prepend_succ {m} (k : Nat) (s : Fin m) (xs : Fin k → Fin m) (i : Fin k) : prepend k s xs i.succ = xs i := rfl

theorem prepend_map {m j} (k : Nat) (s : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (fun i => ρ (prepend k s xs i)) = prepend k (ρ s) (fun i => ρ (xs i)) := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem constructor_of_payload {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w s args payload two n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (.mem s w)) (hf : Derives Γ (forest k w xs args))
    (hc : Derives Γ (StructuralListSyntax.consCode w s args payload))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 two)) (hn : Derives Γ (StructuralNodeSyntax.raw w two payload n)) :
    Derives Γ (constructor (k+1) 2 w (prepend k s xs) n) := by
  have hForest := intro_cons k w (prepend k s xs) payload args hs hf hc
  have hNode := intro_node (k+1) w two (prepend k s xs) n payload (SyntaxNumerals.range hZ 2 w two hw ht) hForest hn
  exact intro_constructor (k+1) 2 w (prepend k s xs) n two ht hNode

theorem constructor_of_application {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w symbol s args n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (scalar w symbol s)) (hf : Derives Γ (forest k w xs args))
    (ha : Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n)) :
    Derives Γ (constructor (k+1) 2 w (prepend k s xs) n) := by
  let B := OriginalFormulaApplicationSyntax.body w symbol args n
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 h B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
  have hs1 : Derives Δ (scalar (old 3 w) (old 3 symbol) (old 3 s)) := of_eq (scalar_rename w symbol s (old 3)) (lift hs)
  have hf1 : Derives Δ (forest k (old 3 w) (fun i => old 3 (xs i)) (old 3 args)) := of_eq (forest_rename k w xs args (old 3)) (lift hf)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxNodes.unique hZ1 0 (old 3 w) (old 3 symbol) Fin.elim0 (slot 3 0) (old 3 s) hw1 (.conjL hB) hs1
  have hc := StructuralListCodeFields.head_subst (old 3 w) (slot 3 0) (old 3 s) (old 3 args) (slot 3 1) he (.conjL (.conjR hB))
  have ho := constructor_of_payload hZ1 k (old 3 w) (old 3 s) (old 3 args) (slot 3 1) (slot 3 2) (old 3 n) (fun i => old 3 (xs i)) hw1 (SyntaxNodes.range hZ1 0 _ _ _ _ hw1 hs1) hf1 hc (.conjL (.conjR (.conjR hB))) (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [constructor_rename, prepend_map]) ho

theorem application_of_node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w symbol s args two n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (scalar w symbol s)) (hf : Derives Γ (forest k w xs args))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 2 two))
    (hn : Derives Γ (node (k+1) w two (prepend k s xs) n)) :
    Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n) := by
  let N := nodeBody (k+1) w two (prepend k s xs) n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node (k+1) w two (prepend k s xs) n _ hn
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  let C := (Formula.mem s.castSucc.castSucc w.castSucc.castSucc).conj
    ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1))).conj
      (StructuralListSyntax.consCode w.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply Derives.exE (p := C) (Derives.conjL (Derives.conjR hN))
  have hZ2 := ZFContext.under (ZFContext.under hZ N) C
  have lift {p : Formula m} (h : Derives Γ p) : Derives Δ p.raise.raise := under (under h N) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (lift hw)
  have hs2 : Derives Δ (scalar w.castSucc.castSucc symbol.castSucc.castSucc s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, scalar_rename]) (lift hs)
  have hf2 : Derives Δ (forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) args.castSucc.castSucc) := of_eq (by simp only [Formula.raise, forest_rename]) (lift hf)
  have ht2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 two.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (lift ht)
  have hr : Derives Δ (StructuralNodeSyntax.raw w.castSucc.castSucc two.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralNodeSyntax.raw_rename]) (under (.conjR (.conjR hN)) C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := SyntaxForests.unique hZ2 k _ _ _ _ hw2 (.conjL (.conjR hC)) hf2
  have hc := cons_tail_subst _ _ _ _ _ he (.conjR (.conjR hC))
  have ho := OriginalFormulaApplicationSyntax.intro_application _ _ _ _ _ _ _ hs2 hc ht2 hr
  simpa only [Formula.raise, OriginalFormulaApplicationSyntax.application_rename] using ho

theorem application_of_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w symbol s args n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (scalar w symbol s)) (hf : Derives Γ (forest k w xs args))
    (hn : Derives Γ (constructor (k+1) 2 w (prepend k s xs) n)) :
    Derives Γ (OriginalFormulaApplicationSyntax.application w symbol args n) := by
  let B := constructorBody (k+1) 2 w (prepend k s xs) n
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply eliminate_constructor (k+1) 2 w (prepend k s xs) n _ hn
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hs1 : Derives Δ (scalar w.castSucc symbol.castSucc s.castSucc) := of_eq (scalar_rename w symbol s Fin.castSucc) (under hs B)
  have hf1 : Derives Δ (forest k w.castSucc (fun i => (xs i).castSucc) args.castSucc) := of_eq (forest_rename k w xs args Fin.castSucc) (under hf B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := application_of_node hZ1 k w.castSucc symbol.castSucc s.castSucc args.castSucc (Fin.last m) n.castSucc (fun i => (xs i).castSucc) hw1 hs1 hf1 (.conjL hB) (.conjR hB)
  exact of_eq (OriginalFormulaApplicationSyntax.application_rename w symbol args n Fin.castSucc).symm ho

theorem application_iff_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat)
    (w symbol s args n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hs : Derives Γ (scalar w symbol s)) (hf : Derives Γ (forest k w xs args)) :
    Derives Γ ((OriginalFormulaApplicationSyntax.application w symbol args n).iff (constructor (k+1) 2 w (prepend k s xs) n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact constructor_of_application (ZFContext.add hZ _) k w symbol s args n xs (add hw _) (add hs _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact application_of_constructor (ZFContext.add hZ _) k w symbol s args n xs (add hw _) (add hs _) (add hf _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalFormulaApplicationNodes
