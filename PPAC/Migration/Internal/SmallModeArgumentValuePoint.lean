import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.SmallModeArgumentHeadTailFiber

/-! 从真实较小尾码的归纳性质和实际头Promise取得父列表唯一输出。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentValuePoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax OriginalArgumentValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d n k h t : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (he : Derives Γ (OriginalArgumentValueSyntax.earlier w mode depth parameter a b c d n))
    (hhN : Derives Γ (Formula.mem h w))
    (htN : Derives Γ (Formula.mem t w))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hparts : Derives Γ (TypedArgumentListElimination.consParts w k a b h t))
    : Derives Γ (fiber w mode depth parameter k c d n) := by
  have htn := Derives.conjR (StructuralConsCore.components hZ w h t n hw hhN htN hci)
  let B := ((Formula.mem (Fin.last m) w.castSucc).conj (successor k.castSucc (Fin.last m))).conj ((SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc h.castSucc).conj (SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc t.castSucc))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hparts
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (under hm B)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hd B)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hp B)
  have hpr1 : Derives Δ (OriginalNumericTermValueSyntax.promise w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (under hpr B)
  have he1 : Derives Δ (OriginalArgumentValueSyntax.earlier w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := of_eq (by simp only [OriginalArgumentValueSyntax.earlier_rename]) (under he B)
  have htN1 : Derives Δ (Formula.mem t.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under htN B)
  have hci1 : Derives Δ (StructuralListSyntax.consCode w.castSucc h.castSucc t.castSucc n.castSucc) := of_eq (by simp only [StructuralListSyntax.consCode_rename]) (under hci B)
  have htn1 : Derives Δ (.mem t.castSucc n.castSucc) := under htn B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hpT := earlier_at w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc t.castSucc he1 htN1 htn1
  have hfT := property_at _ _ _ _ _ _ _ _ _ (Fin.last m) hpT (.conjR (.conjR hB))
  have ho := SmallModeArgumentHeadTailFiber.cons_from_fibers (ZFContext.under hZ B) modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) k.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc h.castSucc t.castSucc hw1 hm1 hd1 hp1 (.conjR (.conjL hB)) hci1 (.conjL (.conjR hB)) hpr1 hfT
  exact of_eq (fiber_rename w mode depth parameter k c d n Fin.castSucc).symm ho

theorem at_source_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d n k : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (he : Derives Γ (OriginalArgumentValueSyntax.earlier w mode depth parameter a b c d n))
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n))
    : Derives Γ (fiber w mode depth parameter k c d n) := by
  have hcases := TypedArgumentListCases.forward hZ w k a b n hw hL
  apply Derives.disjE hcases
  · let E := TypedArgumentListCases.nilCase w k a b n
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    exact SmallModeArgumentValueConstruct.nil_fiber (ZFContext.add hZ E) modeIndex hSmall w mode depth parameter k c d n (add hw E) (add hm E) (add hd E) (add hp E) (.conjL (.conjR hE)) (add hc E) (.conjL hE)
  · let E := TypedArgumentListCases.consCase w k a b n
    let C := TypedArgumentListCases.consBody w k a b n
    let Δ := Context.add C (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 C _ (.hyp (Or.inl rfl))
    have hZ2 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) C
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (by simp only [omega_rename]) (HornBinderRules.under_body 2 (add hw E) C)
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex (old 2 mode)) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (HornBinderRules.under_body 2 (add hm E) C)
    have hd1 : Derives Δ (Formula.mem (old 2 depth) (old 2 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 2 (add hd E) C)
    have hp1 : Derives Δ (Formula.mem (old 2 parameter) (old 2 w)) := of_eq (by simp only [Formula.rename]) (HornBinderRules.under_body 2 (add hp E) C)
    have hpr1 : Derives Δ (OriginalNumericTermValueSyntax.promise (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d)) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (HornBinderRules.under_body 2 (add hpr E) C)
    have he1 : Derives Δ (OriginalArgumentValueSyntax.earlier (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n)) := of_eq (by simp only [OriginalArgumentValueSyntax.earlier_rename]) (HornBinderRules.under_body 2 (add he E) C)
    have hC : Derives Δ C := .hyp (Or.inl rfl)
    have ho := cons_from_earlier hZ2 modeIndex hSmall (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 n) (old 2 k) (slot 2 0) (slot 2 1) hw1 hm1 hd1 hp1 hpr1 he1 (.conjL (.conjL hC)) (.conjR (.conjL hC)) (.conjL (.conjR hC)) (.conjR (.conjR hC))
    exact of_eq (fiber_rename w mode depth parameter k c d n (old 2)).symm ho

theorem property_from_earlier {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter a b c d n : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hc : Derives Γ (SyntaxTermSyntax.contexts w c d))
    (hpr : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (he : Derives Γ (OriginalArgumentValueSyntax.earlier w mode depth parameter a b c d n))
    : Derives Γ (property w mode depth parameter a b c d n) := by
  apply Derives.allI
  apply Derives.impI
  let B := SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc n.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [omega_rename]) (under hw B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc) := of_eq (by simp only [SyntaxNumeralSyntax.numeral_rename]) (under hm B)
  have hd1 : Derives Δ (Formula.mem depth.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hd B)
  have hp1 : Derives Δ (Formula.mem parameter.castSucc w.castSucc) := of_eq (by simp only [Formula.rename]) (under hp B)
  have hc1 : Derives Δ (SyntaxTermSyntax.contexts w.castSucc c.castSucc d.castSucc) := of_eq (by simp only [SyntaxTermSyntax.contexts_rename]) (under hc B)
  have hpr1 : Derives Δ (OriginalNumericTermValueSyntax.promise w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc) := of_eq (by simp only [OriginalNumericTermValueSyntax.promise_rename]) (under hpr B)
  have he1 : Derives Δ (OriginalArgumentValueSyntax.earlier w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) := of_eq (by simp only [OriginalArgumentValueSyntax.earlier_rename]) (under he B)
  exact at_source_list (ZFContext.under hZ B) modeIndex hSmall w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hm1 hd1 hp1 hc1 hpr1 he1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.SmallModeArgumentValuePoint
