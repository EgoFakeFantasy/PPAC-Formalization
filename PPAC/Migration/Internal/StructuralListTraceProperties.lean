import PPAC.Migration.Internal.StructuralListTraceSyntax

/-! 完整轨迹各项对象前提及末值自然范围；不把这些结论作为公理字段。 -/
namespace PPAC.Migration.Internal.StructuralListTraceProperties
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax

theorem zero_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (empty z) :=
  (Derives.conjL (Derives.conjL (Derives.conjL ht)))

theorem nil_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (nilCode w e) :=
  (Derives.conjR (Derives.conjL (Derives.conjL ht)))

theorem length_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (Formula.mem l w) :=
  (Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjL ht))))

theorem successor_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (successor d l) :=
  (Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjL ht))))

theorem sequence_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (sequence f d w) :=
  (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjL ht))))

theorem seed_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (edge f z e) :=
  (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjL ht)))))

theorem links_at_trace {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (links w l f) :=
  (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjL ht)))))

theorem last_at {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (edge f l n) :=
  (Derives.conjR ht)

theorem range {m} {Γ : Context m} (w z e l d f n : Fin m) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (.mem n w) :=
  .impE (SequenceSyntax.bounded_at f w l n (.conjR (sequence_at _ _ _ _ _ _ _ ht))) (last_at _ _ _ _ _ _ _ ht)

theorem domain_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (.mem d w) :=
  OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw
    (length_at _ _ _ _ _ _ _ ht) (successor_at _ _ _ _ _ _ _ ht)
end PPAC.Migration.Internal.StructuralListTraceProperties
