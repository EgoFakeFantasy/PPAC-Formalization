import PPAC.Migration.Internal.StructuralListPositionSyntax

/-! 取尾零步由原末边和完整图单值性对齐，不以宿主解码函数定义。 -/
namespace PPAC.Migration.Internal.StructuralListPositionBase
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax NaturalAdditionSyntax StructuralListProjectionSyntax StructuralListPositionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r k y : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w)) (hn : Derives Γ (edge f l n))
    (hr : Derives Γ (empty r)) (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l))
    (hy : Derives Γ (edge f k y)) : Derives Γ (iteration false w n r y) := by
  have hrW := OmegaStructureAlgebra.zero_member w r (ZFContext.arithmetic hZ).base.extensionality hw hr
  have hkr := ZFArithmetic.add_commute hZ w r k l hw hrW hk hs
  have hlk := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (NaturalAdditionSyntax.params w) w k r l hr hkr
  have hly := StructuralListTraceOrder.edge_input_subst f k l y (eq_symm hlk) hy
  have heq := GraphProperties.single_valued f d l y n (ZFContext.arithmetic hZ).base.extensionality (.conjL hf) hly hn
  exact StructuralListIterationTransport.value_subst false w n r n y (eq_symm heq) (StructuralListPositionLogic.zero_value hZ false w n r hw hr)

theorem positions_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l d f n r : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (sequence f d w)) (hn : Derives Γ (edge f l n))
    (hr : Derives Γ (empty r)) : Derives Γ (positions w l f n r) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let A := (((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
    (sum w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc)).conj
    (edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))
  let Δ := Context.add A (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ A
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise := OrderedPairElimination.under_two hq A
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hf2 : Derives Δ (sequence f.castSucc.castSucc d.castSucc.castSucc w.castSucc.castSucc) := by simpa only [Formula.raise, sequence_rename] using lift hf
  have hn2 : Derives Δ (edge f.castSucc.castSucc l.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, edge_rename] using lift hn
  have hr2 : Derives Δ (empty r.castSucc.castSucc) := by simpa only [Formula.raise, empty_rename] using lift hr
  have hA : Derives Δ A := .hyp (Or.inl rfl)
  exact zero_point hZ2 _ _ _ _ _ _ _ _ hw2 hf2 hn2 hr2 (.conjL (.conjL hA)) (.conjR (.conjL hA)) (.conjR hA)
end PPAC.Migration.Internal.StructuralListPositionBase
