import PPAC.Migration.Internal.ObjectGodelUnpair

/-! 原始结构节点为配数后的实际后继；标签和载荷均为内部自然对象。 -/
namespace PPAC.Migration.Internal.StructuralNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax

def rawWitness {m} (w tag payload n : Fin m) : Formula (m+1) :=
  (GodelPairSyntax.code w.castSucc tag.castSucc payload.castSucc (Fin.last m)).conj (successor n.castSucc (Fin.last m))
def raw {m} (w tag payload n : Fin m) : Formula m := .ex (rawWitness w tag payload n)
def existsRaw {m} (w tag payload : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (raw w.castSucc tag.castSucc payload.castSucc (Fin.last m)))
def encodeFiber {m} (w tag payload : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (raw w.castSucc tag.castSucc payload.castSucc (Fin.last m))).conj (.all
    ((raw w.castSucc.castSucc tag.castSucc.castSucc payload.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem raw_rename {m k} (w tag payload n : Fin m) (r : Fin m → Fin k) :
    (raw w tag payload n).rename r = raw (r w) (r tag) (r payload) (r n) := by
  simp only [raw, rawWitness, Formula.rename, GodelPairSyntax.code_rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existsRaw_rename {m k} (w tag payload : Fin m) (r : Fin m → Fin k) :
    (existsRaw w tag payload).rename r = existsRaw (r w) (r tag) (r payload) := by
  simp only [existsRaw, Formula.rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem encodeFiber_rename {m k} (w tag payload : Fin m) (r : Fin m → Fin k) :
    (encodeFiber w tag payload).rename r = encodeFiber (r w) (r tag) (r payload) := by
  simp only [encodeFiber, Formula.rename, raw_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_raw {m} {Γ : Context m} (w tag payload n q : Fin m)
    (hq : Derives Γ (GodelPairSyntax.code w tag payload q)) (hn : Derives Γ (successor n q)) : Derives Γ (raw w tag payload n) := by
  apply Derives.exI q
  simp only [Formula.instantiate, rawWitness, Formula.rename, GodelPairSyntax.code_rename, successor_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hq hn

theorem eliminate_raw {m} {Γ : Context m} (w tag payload n : Fin m) (r : Formula m) (hn : Derives Γ (raw w tag payload n))
    (hc : Derives (Context.add (rawWitness w tag payload n) (Context.image Formula.raise Γ)) r.raise) : Derives Γ r := .exE hn hc

theorem intro_existsRaw {m} {Γ : Context m} (w tag payload n : Fin m) (hn : Derives Γ (.mem n w))
    (hr : Derives Γ (raw w tag payload n)) : Derives Γ (existsRaw w tag payload) := by
  apply Derives.exI n
  simp only [Formula.instantiate, Formula.rename, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hn hr

theorem output_subst {m} {Γ : Context m} (w tag payload n p : Fin m) (he : Derives Γ (.equal n p))
    (hn : Derives Γ (raw w tag payload n)) : Derives Γ (raw w tag payload p) := by
  have hi : Derives Γ ((raw w.castSucc tag.castSucc payload.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (raw w.castSucc tag.castSucc payload.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, raw_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.StructuralNodeSyntax
