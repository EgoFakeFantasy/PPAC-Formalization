import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.SmallModeArgumentOutputUnique

/-! 原Run₂实际值的Nil／Cons对象构造和内部存在见证；唯一性覆盖所有候选。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentValueConstruct
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter k c d n q : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hz : Derives Γ (empty k))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (hq : Derives Γ (StructuralListSyntax.nilCode w q))
    : Derives Γ (value w mode depth parameter k c d n q) := by
  have hr := Derives.impE (.conjR (SmallModeArgumentsRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)) (.disjL (.conjI hn hq))
  apply Derives.conjI hr
  apply Derives.conjI (TypedArgumentListConstruction.nil_list hZ w k c d q hw hz hctx hq)
  apply Derives.allI
  apply Derives.impI
  let E := OriginalTransformRowSyntax.run 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw E)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hm E)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hd E)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hp E)
  have hn1 : Derives Δ (StructuralListSyntax.nilCode w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.nilCode_rename]) (under hn E)
  have hq1 : Derives Δ (StructuralListSyntax.nilCode w.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.nilCode_rename]) (under hq E)
  exact SmallModeArgumentOutputUnique.nil_unique (ZFContext.under hZ E) modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc (Fin.last m) hw1 hm1 hd1 hp1 hn1 hq1 (.hyp (Or.inl rfl))

theorem cons_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter ell k c d n q h t H T : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hs : Derives Γ (successor k ell))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hco : Derives Γ (StructuralListSyntax.consCode w H T q))
    (hh : Derives Γ (OriginalNumericTermValueSyntax.value w mode depth parameter c d h H))
    (ht : Derives Γ (OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T))
    : Derives Γ (value w mode depth parameter k c d n q) := by
  have ho := OriginalArgumentCaseSyntax.intro_cons w mode depth parameter n q h t H T (.conjI (.conjI hci hco) (.conjI (.conjL hh) (.conjL ht)))
  have hr := Derives.impE (.conjR (SmallModeArgumentsRun.run_iff hZ modeIndex hSmall w mode depth parameter n q hw hm hd hp)) (.disjR ho)
  apply Derives.conjI hr
  apply Derives.conjI (TypedArgumentListConstruction.cons_list hZ w ell k c d H T q hw (.conjL (.conjR hh)) (.conjL (.conjR ht)) hco hs)
  apply Derives.allI
  apply Derives.impI
  let E := OriginalTransformRowSyntax.run 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw E)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hm E)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hd E)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hp E)
  have hci1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (under hci E)
  have hco1 : Derives Δ (StructuralListSyntax.consCode w.castSucc H.castSucc T.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (under hco E)
  have hh1 : Derives Δ (OriginalNumericTermValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc h.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, OriginalNumericTermValueSyntax.value_rename]) (under hh E)
  have ht1 : Derives Δ (OriginalArgumentValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc c.castSucc d.castSucc t.castSucc T.castSucc) := of_eq (by simp only [Formula.raise, OriginalArgumentValueSyntax.value_rename]) (under ht E)
  exact SmallModeArgumentOutputUnique.cons_unique (ZFContext.under hZ E) modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc c.castSucc d.castSucc n.castSucc q.castSucc h.castSucc t.castSucc H.castSucc T.castSucc (Fin.last m) hw1 hm1 hd1 hp1 hci1 hco1 hh1 ht1 (.hyp (Or.inl rfl))

theorem nil_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter k c d n : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hz : Derives Γ (empty k))
    (hctx : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    : Derives Γ (fiber w mode depth parameter k c d n) :=
  intro_fiber w mode depth parameter k c d n n (nil_value hZ modeIndex hSmall w mode depth parameter k c d n n hw hm hd hp hz hctx hn hn)

theorem cons_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter ell k c d n h t H T : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hs : Derives Γ (successor k ell))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hh : Derives Γ (OriginalNumericTermValueSyntax.value w mode depth parameter c d h H))
    (ht : Derives Γ (OriginalArgumentValueSyntax.value w mode depth parameter ell c d t T))
    : Derives Γ (fiber w mode depth parameter k c d n) := by
  have he := StructuralConsCore.exists_cons hZ w H T hw (OriginalNumericTermValueSyntax.output_natural _ _ _ _ _ _ _ _ hh) (OriginalArgumentValueSyntax.output_natural _ _ _ _ _ _ _ _ _ ht)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListSyntax.consCode w.castSucc H.castSucc T.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw E)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hm E)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hd E)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under hp E)
  have hs1 : Derives Δ (successor k.castSucc ell.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hs E)
  have hci1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (under hci E)
  have hh1 : Derives Δ (OriginalNumericTermValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc h.castSucc H.castSucc) := of_eq (by simp only [Formula.raise, OriginalNumericTermValueSyntax.value_rename]) (under hh E)
  have ht1 : Derives Δ (OriginalArgumentValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc c.castSucc d.castSucc t.castSucc T.castSucc) := of_eq (by simp only [Formula.raise, OriginalArgumentValueSyntax.value_rename]) (under ht E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hv := cons_value (ZFContext.under hZ E) modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc k.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) h.castSucc t.castSucc H.castSucc T.castSucc hw1 hm1 hd1 hp1 hs1 hci1 (.conjR hE) hh1 ht1
  exact of_eq (fiber_rename w mode depth parameter k c d n Fin.castSucc).symm (intro_fiber _ _ _ _ _ _ _ _ _ hv)

end PPAC.Migration.Internal.SmallModeArgumentValueConstruct
