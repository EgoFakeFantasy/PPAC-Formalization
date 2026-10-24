import PPAC.Migration.Internal.ProofForallNodeSyntax
import PPAC.Migration.Internal.ProofForallHead

/-! 原forall模式完整有界节点与公式／完整mode1程序／前驱字段规格对象等价，搜索界已实际消去。 -/
namespace PPAC.Migration.Internal.ProofForallNode
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax ProofForallNodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((boundedMatrix w row env).iff (specificationMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := boundedMatrix w row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hm := Derives.conjR (.conjR hE)
    have hs := Derives.impE (.conjL (ProofForallAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR hm)
    exact .conjI hn (.conjI (.conjL hm) hs)
  · apply Derives.impI
    let E := specificationMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.conjL (.conjR hE)
    have hb := Derives.impE (.conjR (ProofForallAllQueries.bundle_iff (ZFContext.add hZ E) w z env (add hw E) hn (add hz E))) (.conjR (.conjR hE))
    have hpredecessorFormula := Derives.conjL (.conjR (.conjR hb))
    have hbound := ProofForallBounds.environment_bound (ZFContext.add hZ E) w row env (add hw E) hn hh hpredecessorFormula
    exact .conjI hn (.conjI hbound (.conjI hh hb))

theorem node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (specification w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hw6 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hz6 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact matrix_iff (HornBinderRules.zf_many 4 hZ) (old 4 w) (old 4 z) (old 4 row) (slot 4) hw6 hz6

def normalizedMatrix {m} (w z row : Fin m) (env : Fin 4 → Fin m) : Formula m :=
  (environmentNat 4 w env).conj ((ProofForallHead.normalized w row env).conj (ProofForallSyntax.specification w z env))

def normalizedBody {m} (w z row : Fin m) : Formula (m+4) :=
  normalizedMatrix (old 4 w) (old 4 z) (old 4 row) (slot 4)

def normalized {m} (w z row : Fin m) : Formula m := existsMany 4 (normalizedBody w z row)

theorem specification_normalized_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m) (env : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((specificationMatrix w z row env).iff (normalizedMatrix w z row env)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := specificationMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjL (ProofForallHead.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))
  · apply Derives.impI
    let E := normalizedMatrix w z row env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hn := Derives.conjL hE
    have hh := Derives.impE (.conjR (ProofForallHead.head_iff (ZFContext.add hZ E) w row env (add hw E) hn)) (.conjL (.conjR hE))
    exact .conjI hn (.conjI hh (.conjR (.conjR hE)))

theorem normalized_node_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z row : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((node w row).iff (normalized w z row)) := by
  apply HornApplicationBounds.existsMany_congr 4
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_many 4 hw)
  have hz4 := of_eq (empty_rename z (old 4)) (HornBinderRules.under_many 4 hz)
  exact SyntaxTypeLocalTransfer.iff_trans
    (matrix_iff (HornBinderRules.zf_many 4 hZ) (old 4 w) (old 4 z) (old 4 row) (slot 4) hw4 hz4)
    (specification_normalized_iff (HornBinderRules.zf_many 4 hZ) (old 4 w) (old 4 z) (old 4 row) (slot 4) hw4)

end PPAC.Migration.Internal.ProofForallNode
