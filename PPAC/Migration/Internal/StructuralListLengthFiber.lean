import PPAC.Migration.Internal.StructuralListLengthUnique

/-! 每个有效内部列表码有实际唯一自然长度；任意两条同码轨迹的长度相等。 -/
namespace PPAC.Migration.Internal.StructuralListLengthFiber
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListTraceSyntax StructuralListLengthSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem trace_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n s u k b g : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (trace w z e l d f n)) (hg : Derives Γ (trace w s u k b g n)) : Derives Γ (.equal l k) :=
  StructuralListLengthUnique.unique hZ w n l k hw (intro_length w n l z e d f hf) (intro_length w n k s u b g hg)

theorem unique_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (valid w n)) : Derives Γ (StructuralListLengthSyntax.fiber w n) := by
  have hl := StructuralListLengthBasic.exists_length w n hv
  let L := (Formula.mem (Fin.last m) w.castSucc).conj (hasLength w.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  change Derives Γ (.ex L) at hl
  apply Derives.exE (p := L) hl
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hu : Derives Ξ (.all ((hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let K := hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add K (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 K
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 K
    have hOld : Derives Δ (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, hasLength_rename] using under (Derives.conjR hL) K
    exact StructuralListLengthUnique.unique hZ2 _ _ _ _ hw2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (StructuralListLengthSyntax.fiber w.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, hasLength_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hL hu
  simpa only [Formula.raise, StructuralListLengthSyntax.fiber_rename] using hout
end PPAC.Migration.Internal.StructuralListLengthFiber
