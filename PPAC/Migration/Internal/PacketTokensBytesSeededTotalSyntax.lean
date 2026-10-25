import PPAC.Migration.Internal.PacketTokensBytesSeeded

/-! All-tail actual seeded fibers and a fixed object induction matrix indexed by the actual prefix code. -/
namespace PPAC.Migration.Internal.PacketTokensBytesSeededTotalSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokensBytesSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniqueAt {m} (w n t a : Fin m) : Formula m := .all
  ((seeded w.castSucc n.castSucc t.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiberBody {m} (w n t : Fin m) : Formula (m+1) :=
  ((Formula.mem (Fin.last m) w.castSucc).conj (seeded w.castSucc n.castSucc t.castSucc (Fin.last m))).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m))

def fiber {m} (w n t : Fin m) : Formula m := .ex (fiberBody w n t)

def property {m} (w n : Fin m) : Formula m := (StructuralListTraceSyntax.valid w n).imp (.all
  ((StructuralListTraceSyntax.valid w.castSucc (Fin.last m)).imp (fiber w.castSucc n.castSucc (Fin.last m))))

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def matrix : Formula 2 := property 0 1

theorem uniqueAt_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAt w n t a).rename ρ = uniqueAt (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [uniqueAt,Formula.rename,seeded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiberBody_lift {m k} (w n t : Fin m) (ρ : Fin m → Fin k) :
    (fiberBody w n t).rename (Formula.liftRen ρ) = fiberBody (ρ w) (ρ n) (ρ t) := by
  simp only [fiberBody,Formula.rename,seeded_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n t : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n t).rename ρ = fiber (ρ w) (ρ n) (ρ t) := by
  simp only [fiber,Formula.rename,fiberBody_lift]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,StructuralListTraceSyntax.valid_rename,fiber_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) : MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,property_rename,h0,h1]

theorem unique_at {m} {Γ : Context m} (w n t a b : Fin m) (hu : Derives Γ (uniqueAt w n t a))
    (hb : Derives Γ (seeded w n t b)) : Derives Γ (.equal b a) := by
  have hh : Derives Γ ((seeded w n t b).imp (.equal b a)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,seeded_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE b hu)
  exact .impE hh hb

theorem at_tail {m} {Γ : Context m} (w n t : Fin m) (hp : Derives Γ (property w n))
    (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) (ht : Derives Γ (StructuralListTraceSyntax.valid w t)) : Derives Γ (fiber w n t) := by
  have hh : Derives Γ ((StructuralListTraceSyntax.valid w t).imp (fiber w n t)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListTraceSyntax.valid_rename,fiber_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE t (.impE hp hn))
  exact .impE hh ht

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (hi : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hb : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hh : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property w x))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE x hi)
  exact .impE (.impE hh hx) hb

theorem intro_fiber {m} {Γ : Context m} (w n t a : Fin m) (ha : Derives Γ (.mem a w))
    (hs : Derives Γ (seeded w n t a)) (hu : Derives Γ (uniqueAt w n t a)) : Derives Γ (fiber w n t) := by
  apply Derives.exI a
  exact of_eq (by simp only [fiberBody,Formula.instantiate,Formula.rename,seeded_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjI ha hs) hu)

theorem push_input {m} {Γ : Context m} (w h x y n : Fin m) (he : Derives Γ (.equal x y))
    (hc : Derives Γ (PacketTokensBytesRowSyntax.push w h x n)) : Derives Γ (PacketTokensBytesRowSyntax.push w h y n) := by
  let P := PacketTokensBytesRowSyntax.push w.castSucc h.castSucc (Fin.last m) n.castSucc
  have h0 : P.instantiate x = PacketTokensBytesRowSyntax.push w h x n := by simp only [P,Formula.instantiate,PacketTokensBytesRowSyntax.push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate y = PacketTokensBytesRowSyntax.push w h y n := by simp only [P,Formula.instantiate,PacketTokensBytesRowSyntax.push_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

end PPAC.Migration.Internal.PacketTokensBytesSeededTotalSyntax
