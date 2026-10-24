import PPAC.Migration.Internal.PacketTokenRuleData

/-! Token rows retain their actual tag and three ordered internal fields. -/
namespace PPAC.Migration.Internal.PacketTokenSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def tagRow {m} (tag : Nat) (w a b c r : Fin m) : Formula m := SyntaxNodeSyntax.constructor 3 tag w (SyntaxAtomSyntax.three a b c) r

def tagEntry {m} (tag : Nat) (w V a b c : Fin m) : Formula m := .ex
  ((tagRow tag w.castSucc a.castSucc b.castSucc c.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc))

def row {m} (w n t a r : Fin m) : Formula m := tagRow 2 w n t a r

def entry {m} (w V n t a : Fin m) : Formula m := tagEntry 2 w V n t a

def small {m} (w B V n t a r : Fin m) : Formula m :=
  (row w n t a r).conj ((Formula.mem n B).conj (tagEntry 1 w V n t a))

def largeAt {m} (w B V z y r : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (row w (env 0) (env 1) (env 2) r).conj (((Formula.mem z (env 4)).conj (.mem (env 3) B)).conj
    ((tagEntry 0 w V (env 3) (env 4) (env 0)).conj
      ((entry w V (env 4) (env 1) (env 5)).conj (tagEntry 1 w V y (env 5) (env 2)))))

def largeBody {m} (w B V r : Fin m) (env : Fin 6 → Fin m) : Formula (m+2) :=
  (empty (slot 2 0)).conj ((NaturalAdditionSyntax.sum (old 2 w) (old 2 (env 3)) (old 2 B) (slot 2 1)).conj
    (largeAt (old 2 w) (old 2 B) (old 2 V) (slot 2 0) (slot 2 1) (old 2 r) (fun i => old 2 (env i))))

def large {m} (w B V r : Fin m) (env : Fin 6 → Fin m) : Formula m := existsMany 2 (largeBody w B V r env)

theorem tagRow_rename {m j} (tag : Nat) (w a b c r : Fin m) (ρ : Fin m → Fin j) :
    (tagRow tag w a b c r).rename ρ = tagRow tag (ρ w) (ρ a) (ρ b) (ρ c) (ρ r) := by
  simp only [tagRow, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem tagEntry_rename {m j} (tag : Nat) (w V a b c : Fin m) (ρ : Fin m → Fin j) :
    (tagEntry tag w V a b c).rename ρ = tagEntry tag (ρ w) (ρ V) (ρ a) (ρ b) (ρ c) := by
  simp only [tagEntry, Formula.rename, tagRow_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem row_rename {m j} (w n t a r : Fin m) (ρ : Fin m → Fin j) :
    (row w n t a r).rename ρ = row (ρ w) (ρ n) (ρ t) (ρ a) (ρ r) := tagRow_rename 2 w n t a r ρ

theorem entry_rename {m j} (w V n t a : Fin m) (ρ : Fin m → Fin j) :
    (entry w V n t a).rename ρ = entry (ρ w) (ρ V) (ρ n) (ρ t) (ρ a) := tagEntry_rename 2 w V n t a ρ

theorem small_rename {m j} (w B V n t a r : Fin m) (ρ : Fin m → Fin j) :
    (small w B V n t a r).rename ρ = small (ρ w) (ρ B) (ρ V) (ρ n) (ρ t) (ρ a) (ρ r) := by
  simp only [small, Formula.rename, row_rename, tagEntry_rename]

theorem largeAt_rename {m j} (w B V z y r : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (largeAt w B V z y r env).rename ρ = largeAt (ρ w) (ρ B) (ρ V) (ρ z) (ρ y) (ρ r) (fun i => ρ (env i)) := by
  simp only [largeAt, Formula.rename, row_rename, tagEntry_rename, entry_rename]

theorem largeBody_lift {m j} (w B V r : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (largeBody w B V r env).rename (lift 2 ρ) = largeBody (ρ w) (ρ B) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [largeBody, Formula.rename, empty_rename, NaturalAdditionSyntax.sum_rename, largeAt_rename, lift_old, lift_slot]

theorem large_rename {m j} (w B V r : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (large w B V r env).rename ρ = large (ρ w) (ρ B) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [large, existsMany_rename, largeBody_lift]

theorem intro_large {m} {Γ : Context m} (w B V r z y : Fin m) (env : Fin 6 → Fin m)
    (hz : Derives Γ (empty z)) (hy : Derives Γ (NaturalAdditionSyntax.sum w (env 3) B y))
    (ha : Derives Γ (largeAt w B V z y r env)) : Derives Γ (large w B V r env) := by
  apply HornBinderRules.intro_many 2 (largeBody w B V r env) (SyntaxAtomSyntax.two z y)
  exact of_eq (by simp only [largeBody, Formula.rename, empty_rename, NaturalAdditionSyntax.sum_rename,
    largeAt_rename, assign_old, assign_slot]; rfl) (.conjI hz (.conjI hy ha))

end PPAC.Migration.Internal.PacketTokenSyntax
