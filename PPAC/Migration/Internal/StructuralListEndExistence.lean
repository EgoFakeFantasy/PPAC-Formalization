import PPAC.Migration.Internal.StructuralListEndInduction

/-! 实际终端见证、长度/值对唯一和原迹Nil种子的真实恢复。 -/
namespace PPAC.Migration.Internal.StructuralListEndExistence
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListProjectionSyntax StructuralListLengthSyntax StructuralListEndSyntax
open StructuralListTraceSyntax (valid trace)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l k y z : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (hasLength w n l)) (hk : Derives Γ (hasLength w n k))
    (hy : Derives Γ (iteration false w n l y)) (hz : Derives Γ (iteration false w n k z)) : Derives Γ ((Formula.equal l k).conj (.equal y z)) := by
  have heq := StructuralListLengthUnique.unique hZ w n l k hw hl hk
  have hyk := StructuralListIterationTransport.index_subst false w n l k y heq hy
  exact .conjI heq (StructuralListIterationTransport.unique hZ false w n k y z hw (StructuralListLengthBasic.length_member w n k hk) hyk hz)

theorem exists_terminal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (existsTerminal w n) := by
  have hl := StructuralListLengthBasic.exists_length w n hv
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at hl
  apply Derives.exE (p := L) hl
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hy := StructuralListIterationTransport.exists_value hZ1 false w.castSucc n.castSucc (Fin.last m) hw1 (.conjL hL)
  let Y := iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 Y
  have hL2 : Derives Δ ((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)) := by
    simpa only [L, Formula.raise, Formula.rename, hasLength_rename] using under hL Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hnil := StructuralListEndInduction.terminal hZ2 _ _ _ _ hw2 (.conjR hL2) hY
  have hout := intro_terminal _ _ _ _ (.conjL hL2) (.conjR hL2) hY hnil
  simpa only [Formula.raise, existsTerminal_rename] using hout

theorem trace_seed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w z e l d f n))
    (hy : Derives Γ (iteration false w n l y)) : Derives Γ (.equal y e) := by
  have hl := StructuralListLengthSyntax.intro_length w n l z e d f ht
  have hnil := StructuralListEndInduction.terminal hZ w n l y hw hl hy
  exact StructuralNil.unique hZ w y e hw hnil (StructuralListTraceProperties.nil_at _ _ _ _ _ _ _ ht)

theorem trace_recovery {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (iteration false w n l e) := by
  have hy := StructuralListIterationTransport.exists_value hZ false w n l hw (StructuralListTraceProperties.length_at _ _ _ _ _ _ _ ht)
  let Y := iteration false w.castSucc n.castSucc l.castSucc (Fin.last m)
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ Y
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have ht1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by
    simpa only [Formula.raise, StructuralListTraceSyntax.trace_rename] using under ht Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have heq := trace_seed hZ1 _ _ _ _ _ _ _ _ hw1 ht1 hY
  have hout := StructuralListIterationTransport.value_subst false _ _ _ _ _ heq hY
  simpa only [Formula.raise, iteration_rename] using hout
end PPAC.Migration.Internal.StructuralListEndExistence
