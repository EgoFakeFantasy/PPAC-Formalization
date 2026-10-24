import PPAC.Migration.Internal.SmallModeArgumentsRun
import PPAC.Migration.Internal.SmallModeArgumentValueConstruct

/-! 实际头Promise与实际尾Fiber经原存在量词消去组装为父列表Fiber。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentHeadTailFiber
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_from_fibers {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4)
    (w mode depth parameter ell k a b c d n h t : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hd : Derives Γ (Formula.mem depth w))
    (hp : Derives Γ (Formula.mem parameter w))
    (hs : Derives Γ (successor k ell))
    (hci : Derives Γ (StructuralListSyntax.consCode w h t n))
    (hh : Derives Γ (SyntaxTermSyntax.term w a b h))
    (hpromise : Derives Γ (OriginalNumericTermValueSyntax.promise w mode depth parameter a b c d))
    (ht : Derives Γ (OriginalArgumentValueSyntax.fiber w mode depth parameter ell c d t))
    : Derives Γ (fiber w mode depth parameter k c d n) := by
  have hfH := OriginalNumericTermValueSyntax.promise_at w mode depth parameter a b c d h hpromise hh
  let Q := OriginalNumericTermValueSyntax.value w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc h.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hfH
  have ht1 : Derives Δ (fiber w.castSucc mode.castSucc depth.castSucc parameter.castSucc ell.castSucc c.castSucc d.castSucc t.castSucc) := of_eq (fiber_rename w mode depth parameter ell c d t Fin.castSucc) (under ht Q)
  let V := value w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc ell.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) ht1
  have hZ2 := ZFContext.under (ZFContext.under hZ Q) V
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw Q) V)
  have hm2 : Derives Ξ (SyntaxNumeralSyntax.numeral modeIndex mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (under hm Q) V)
  have hd2 : Derives Ξ (Formula.mem depth.castSucc.castSucc w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under hd Q) V)
  have hp2 : Derives Ξ (Formula.mem parameter.castSucc.castSucc w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, Formula.rename]) (under (under hp Q) V)
  have hs2 : Derives Ξ (successor k.castSucc.castSucc ell.castSucc.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under (under hs Q) V)
  have hci2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, StructuralListSyntax.consCode_rename]) (under (under hci Q) V)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hHead : Derives Ξ (OriginalNumericTermValueSyntax.value w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc h.castSucc.castSucc (Fin.last m).castSucc) := of_eq (OriginalNumericTermValueSyntax.value_rename w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc h.castSucc (Fin.last m) Fin.castSucc) (under hQ V)
  have ho := SmallModeArgumentValueConstruct.cons_fiber hZ2 modeIndex hSmall w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc ell.castSucc.castSucc k.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hm2 hd2 hp2 hs2 hci2 hHead (.hyp (Or.inl rfl))
  simpa only [Formula.raise, fiber_rename] using ho

end PPAC.Migration.Internal.SmallModeArgumentHeadTailFiber
