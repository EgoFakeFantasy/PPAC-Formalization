import PPAC.Migration.Internal.HornRuleValue

/-! 上游两个真实lookup规则的完整局部矩阵及实际前提成员的纯对象等价。 -/
namespace PPAC.Migration.Internal.OriginalLookupRuleMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornRuleSyntax OriginalLookupExpr
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (lookupHead lookupTail)

theorem rowFields_map {m k} (a b c : Fin m) (ρ : Fin m → Fin k) :
    (fun i => ρ (rowFields a b c i)) = rowFields (ρ a) (ρ b) (ρ c) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i

def childMember {m} (w trace : Fin m) (env : Fin 4 → Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 3 0 w.castSucc (rowFields (env 1).castSucc (env 2).castSucc (env 3).castSucc) (Fin.last m)).conj (.mem (Fin.last m) trace.castSucc))

theorem childMember_rename {m k} (w trace : Fin m) (env : Fin 4 → Fin m) (ρ : Fin m → Fin k) :
    (childMember w trace env).rename ρ = childMember (ρ w) (ρ trace) (fun i => ρ (env i)) := by
  simp only [childMember, Formula.rename, SyntaxNodeSyntax.constructor_rename, rowFields_map, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem head_matrix_iff_graph {m} {Γ : Context m} (w row trace : Fin m) (env : Fin 2 → Fin m) :
    Derives Γ ((matrix lookupHead w row trace env).iff (graph lookupHead.head w env row)) := by
  apply Derives.conjI
  · exact .impI (.conjL (.hyp (Or.inl rfl)))
  · exact .impI (.conjI (.hyp (Or.inl rfl)) (.conjI truth_proved truth_proved))

theorem tail_matrix_iff_graph {m} {Γ : Context m} (w row trace : Fin m) (env : Fin 4 → Fin m) :
    Derives Γ ((matrix lookupTail w row trace env).iff ((graph lookupTail.head w env row).conj (premise premiseExpr w trace env))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hh : Derives (Context.add (matrix lookupTail w row trace env) Γ) (matrix lookupTail w row trace env) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hh) (.conjL (.conjR (.conjR hh)))
  · apply Derives.impI
    have hh : Derives (Context.add ((graph lookupTail.head w env row).conj (premise premiseExpr w trace env)) Γ)
      ((graph lookupTail.head w env row).conj (premise premiseExpr w trace env)) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hh) (.conjI truth_proved (.conjI (.conjR hh) truth_proved))

theorem child_member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w trace : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env)) :
    Derives Γ ((premise premiseExpr w trace env).iff (childMember w trace env)) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename 4 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr (OriginalLookupExpr.premise_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)
    (SyntaxTypeLocalTransfer.iff_refl (.mem (Fin.last m) trace.castSucc))

theorem head_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n z row trace : Fin m) (env : Fin 2 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 2 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n)) (hz : Derives Γ (empty z)) :
    Derives Γ ((matrix lookupHead w row trace env).iff (SyntaxNodeSyntax.constructor 3 0 w (rowFields n z (env 0)) row)) :=
  SyntaxTypeLocalTransfer.iff_trans (head_matrix_iff_graph w row trace env) (OriginalLookupExpr.head_iff hZ w n z row env hw hn hc hz)

theorem tail_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s row trace : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 4 w env))
    (hc : Derives Γ (StructuralListSyntax.consCode w (env 0) (env 1) n)) (hs : Derives Γ (successor s (env 2))) :
    Derives Γ ((matrix lookupTail w row trace env).iff
      ((SyntaxNodeSyntax.constructor 3 0 w (rowFields n s (env 3)) row).conj (childMember w trace env))) :=
  SyntaxTypeLocalTransfer.iff_trans (tail_matrix_iff_graph w row trace env)
    (FormulaCodeCongruence.conj_congr (OriginalLookupExpr.tail_iff hZ w n s row env hw hn hc hs) (child_member_iff hZ w trace env hw hn))

end PPAC.Migration.Internal.OriginalLookupRuleMatrix
