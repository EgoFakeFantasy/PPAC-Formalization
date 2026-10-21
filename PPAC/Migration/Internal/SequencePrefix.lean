import PPAC.Migration.Internal.SequenceExistence
import PPAC.Migration.RestrictionExistence

/-! 一个明确Separation实例实际取得完整序列前缀、精确边及唯一实际图。 -/
namespace PPAC.Migration.Internal.SequencePrefix
open Source SourceAlgebra SourceLogic GraphSyntax SequenceSyntax

def witness {m} (g f n b : Fin m) : Formula m := (sequence g n b).conj
  ((RestrictionSyntax.restrict g f n).conj (RestrictionSyntax.edgeLaw g f n))
def existsPrefix {m} (f n b : Fin m) : Formula m := .ex (witness (Fin.last m) f.castSucc n.castSucc b.castSucc)

theorem witness_rename {m k} (g f n b : Fin m) (r : Fin m → Fin k) :
    (witness g f n b).rename r = witness (r g) (r f) (r n) (r b) := by
  simp only [witness, Formula.rename, sequence_rename, RestrictionSyntax.restrict_rename, RestrictionSyntax.edgeLaw_rename]
theorem existsPrefix_rename {m k} (f n b : Fin m) (r : Fin m → Fin k) :
    (existsPrefix f n b).rename r = existsPrefix (r f) (r n) (r b) := by
  simp only [existsPrefix, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem restricted_bounded {m} {Γ : Context m} (g f n b : Fin m)
    (hf : Derives Γ (bounded f b)) (hr : Derives Γ (RestrictionSyntax.restrict g f n)) : Derives Γ (bounded g b) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hf' : Derives Δ (bounded f.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, bounded_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hr' : Derives Δ (RestrictionSyntax.restrict g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.restrict_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr)
  apply Derives.impI
  exact .impE (add (bounded_at f.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hf') _)
    (RestrictionEdges.old_edge g.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hr' _) (.hyp (Or.inl rfl)))

theorem exists_prefix {m} {Γ : Context m} (f d n b : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation RestrictionSyntax.matrix).rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (sequence f d b)) (hn : Derives Γ (RestrictionSyntax.subset n d)) :
    Derives Γ (existsPrefix f n b) := by
  have hg := RestrictionExistence.exists_function_restriction f d n hs he (.conjL hf) hn
  let G := RestrictionSyntax.witness (Fin.last m) f.castSucc n.castSucc
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hbG : Derives Ξ (bounded f.castSucc b.castSucc) := by
    simpa only [Formula.raise, bounded_rename] using under (.conjR hf) G
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hb := restricted_bounded (Fin.last m) f.castSucc n.castSucc b.castSucc hbG (.conjL hG)
  have hw : Derives Ξ (witness (Fin.last m) f.castSucc n.castSucc b.castSucc) :=
    .conjI (.conjI (.conjL (.conjR hG)) hb) (.conjI (.conjL hG) (.conjR (.conjR hG)))
  have hout : Derives Ξ (existsPrefix f.castSucc n.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw
  simpa only [Formula.raise, existsPrefix_rename] using hout

theorem unique {m} {Γ : Context m} (g h f n b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hg : Derives Γ (witness g f n b)) (hh : Derives Γ (witness h f n b)) : Derives Γ (.equal g h) :=
  RestrictionAlgebra.unique g h f n he (.conjL (.conjR hg)) (.conjL (.conjR hh))
end PPAC.Migration.Internal.SequencePrefix
