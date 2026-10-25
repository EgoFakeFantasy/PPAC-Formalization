import PPAC.Migration.Internal.PacketTokensBytesTracePrefix

/-! Full independent recursive criteria retain actual Cons, smaller folds and exact original Cons construction. -/
namespace PPAC.Migration.Internal.PacketTokensBytesRecursionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketTokensBytesSyntax
open SyntaxRenameQuerySyntax (of_eq)

def nilCase {m} (w n t a : Fin m) : Formula m := (StructuralListSyntax.nilCode w n).conj ((Formula.mem t w).conj (.equal t a))

def terminalBody {m} (w f g p n a : Fin m) : Formula (m+3) :=
  (edge (old 3 f) (old 3 p) (slot 3 1)).conj ((edge (old 3 g) (old 3 p) (slot 3 2)).conj
    ((StructuralListSyntax.consCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 n)).conj
      (PacketTokensBytesRowSyntax.push (old 3 w) (slot 3 0) (slot 3 2) (old 3 a))))

def terminal {m} (w f g p n a : Fin m) : Formula m := existsMany 3 (terminalBody w f g p n a)

def consBody {m} (w n t a : Fin m) : Formula (m+3) :=
  (StructuralListSyntax.consCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 n)).conj
    ((raw (old 3 w) (slot 3 1) (old 3 t) (slot 3 2)).conj
      (PacketTokensBytesRowSyntax.push (old 3 w) (slot 3 0) (slot 3 2) (old 3 a)))

def consCase {m} (w n t a : Fin m) : Formula m := existsMany 3 (consBody w n t a)

def caseAt {m} (w n t a : Fin m) : Formula m := (nilCase w n t a).disj (consCase w n t a)

theorem nilCase_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (nilCase w n t a).rename ρ = nilCase (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [nilCase,Formula.rename,StructuralListSyntax.nilCode_rename]

theorem terminalBody_lift {m k} (w f g p n a : Fin m) (ρ : Fin m → Fin k) :
    (terminalBody w f g p n a).rename (lift 3 ρ) = terminalBody (ρ w) (ρ f) (ρ g) (ρ p) (ρ n) (ρ a) := by
  simp only [terminalBody,Formula.rename,edge_rename,StructuralListSyntax.consCode_rename,PacketTokensBytesRowSyntax.push_rename,lift_old,lift_slot]

theorem terminal_rename {m k} (w f g p n a : Fin m) (ρ : Fin m → Fin k) :
    (terminal w f g p n a).rename ρ = terminal (ρ w) (ρ f) (ρ g) (ρ p) (ρ n) (ρ a) := by
  simp only [terminal,existsMany_rename,terminalBody_lift]

theorem consBody_lift {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (consBody w n t a).rename (lift 3 ρ) = consBody (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,raw_rename,PacketTokensBytesRowSyntax.push_rename,lift_old,lift_slot]

theorem consCase_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (consCase w n t a).rename ρ = consCase (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [consCase,existsMany_rename,consBody_lift]

theorem caseAt_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (caseAt w n t a).rename ρ = caseAt (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [caseAt,Formula.rename,nilCase_rename,consCase_rename]

theorem cons_output {m} {Γ : Context m} (w h x y n : Fin m) (he : Derives Γ (.equal y n))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x y)) : Derives Γ (StructuralListSyntax.consCode w h x n) := by
  let P := StructuralListSyntax.consCode w.castSucc h.castSucc x.castSucc (Fin.last m)
  have h0 : P.instantiate y = StructuralListSyntax.consCode w h x y := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate n = StructuralListSyntax.consCode w h x n := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem intro_terminal {m} {Γ : Context m} (w f g p n a h x u : Fin m)
    (hx : Derives Γ (edge f p x)) (hu : Derives Γ (edge g p u)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (ha : Derives Γ (PacketTokensBytesRowSyntax.push w h u a)) : Derives Γ (terminal w f g p n a) := by
  apply HornBinderRules.intro_many 3 (terminalBody w f g p n a) (SyntaxAtomSyntax.three h x u)
  exact of_eq (by simp only [terminalBody,Formula.rename,edge_rename,StructuralListSyntax.consCode_rename,PacketTokensBytesRowSyntax.push_rename,assign_old,assign_slot]; rfl)
    (.conjI hx (.conjI hu (.conjI hc ha)))

theorem intro_cons {m} {Γ : Context m} (w n t a h x u : Fin m) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hf : Derives Γ (raw w x t u)) (ha : Derives Γ (PacketTokensBytesRowSyntax.push w h u a)) : Derives Γ (consCase w n t a) := by
  apply HornBinderRules.intro_many 3 (consBody w n t a) (SyntaxAtomSyntax.three h x u)
  exact of_eq (by simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,raw_rename,PacketTokensBytesRowSyntax.push_rename,assign_old,assign_slot]; rfl)
    (.conjI hc (.conjI hf ha))

end PPAC.Migration.Internal.PacketTokensBytesRecursionSyntax
