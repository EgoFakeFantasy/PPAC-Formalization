import PPAC.Migration.Internal.ObjectPacketReaderRecursion

/-! Actual terminal digit and continuation-byte equations retain arbitrary value, scale and accumulator, including zero scale. -/
namespace PPAC.Migration.Internal.PacketReaderVarintBranches
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax PacketReaderEvalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem finish_guard {m} {Γ : Context m} (B z o b s : Fin m) (hz : Derives Γ (empty z))
    (hb : Derives Γ (.mem b B)) (hg : Derives Γ ((Formula.equal s o).disj (empty b).neg)) : Derives Γ (finish B z o b s) := by
  apply Derives.conjI hb
  apply Derives.disjE hg
  · exact .disjL (.hyp (Or.inl rfl))
  · apply Derives.disjR
    apply Derives.impI
    have hn : Derives (Context.add (.equal b z) (Context.add (empty b).neg Γ)) (empty b).neg := .hyp (Or.inr (Or.inl rfl))
    exact .impE hn (NaturalMultiplicationLaws.empty_subst z b (eq_symm (.hyp (Or.inl rfl))) (add (add hz _) _))

theorem cons_step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L b T v s a R y S c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hT : Derives Γ (state w T v s a)) (hh : Derives Γ (PacketReaderInputSyntax.headRest w L b T))
    (ht : Derives Γ (step w B z o b T v s a R y S c)) :
    Derives Γ ((eval w B z o L v s a p).iff (eval w B z o R y S c p)) := by
  have hState : Derives Γ (state w L v s a) := .conjI (PacketReaderInputFields.valid_input hZ _ _ _ _ hw hh) (.conjR hT)
  have hAdvance := PacketReaderInputSyntax.intro_advance _ _ _ _ _ _ _ _ _ _ _ _ _ _ hState hh ht
  exact PacketReaderEval.step_iff hZ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hz ho hAdvance

theorem terminal_digit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L b T v s a u c p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hT : Derives Γ (state w T v s a)) (hh : Derives Γ (PacketReaderInputSyntax.headRest w L b T))
    (hb : Derives Γ (.mem b B)) (hg : Derives Γ ((Formula.equal s o).disj (empty b).neg))
    (hu : Derives Γ (PacketAffineSyntax.equation w b v s u)) (hc : Derives Γ (StructuralListSyntax.consCode w u a c)) :
    Derives Γ ((eval w B z o L v s a p).iff (eval w B z o T z o c p)) := by
  have hFinish := finish_guard B z o b s hz hb hg
  have hEmission := PacketReaderEmission.intro_emission _ _ _ _ _ _ _ hu hc
  have hEmit : Derives Γ (emitCase w B z o b T v s a T z o c) :=
    .conjI hFinish (.conjI (.eqRefl T) (.conjI (.eqRefl z) (.conjI (.eqRefl o) hEmission)))
  exact cons_step hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hz ho hT hh (.disjL hEmit)

theorem continuation_byte {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L b T v s a y S p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hT : Derives Γ (state w T v s a)) (hh : Derives Γ (PacketReaderInputSyntax.headRest w L b T))
    (hc : Derives Γ (continuation w B b v s y S)) :
    Derives Γ ((eval w B z o L v s a p).iff (eval w B z o T y S a p)) := by
  have hMore := Derives.conjL (PacketReaderContinuation.domain hZ _ _ _ _ _ _ _ hw hB (.conjL (.conjR hT)) hc)
  have hCont : Derives Γ (continueCase w B b T v s a T y S a) := .conjI hMore (.conjI (.eqRefl T) (.conjI (.eqRefl a) hc))
  exact cons_step hZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hz ho hT hh (.disjR hCont)

theorem continuation_digit {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o L b T v s a d y S p : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hz : Derives Γ (empty z)) (ho : Derives Γ (.mem o w))
    (hT : Derives Γ (state w T v s a)) (hh : Derives Γ (PacketReaderInputSyntax.headRest w L b T))
    (hd : Derives Γ (.mem d w)) (hb : Derives Γ (NaturalAdditionSyntax.sum w d B b))
    (hy : Derives Γ (PacketAffineSyntax.equation w d v s y)) (hS : Derives Γ (NaturalMultiplicationSyntax.product w s B S)) :
    Derives Γ ((eval w B z o L v s a p).iff (eval w B z o T y S a p)) := by
  have hSum := ZFArithmetic.add_commute hZ w d B b hw hd hB hb
  have hCont := PacketReaderContinuation.intro_continuation _ _ _ _ _ _ _ _ hd hSum hy hS
  exact continuation_byte hZ _ _ _ _ _ _ _ _ _ _ _ _ _ hw hB hz ho hT hh hCont

end PPAC.Migration.Internal.PacketReaderVarintBranches
