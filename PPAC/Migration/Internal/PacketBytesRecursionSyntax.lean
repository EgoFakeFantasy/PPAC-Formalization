import PPAC.Migration.Internal.PacketBytesTracePrefix

/-! Full independent recursive criteria retain actual Cons, smaller folds and exact original byte acceptance. -/
namespace PPAC.Migration.Internal.PacketBytesRecursionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketBytesTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

def nilCase {m} (w n t a : Fin m) : Formula m := (StructuralListSyntax.nilCode w n).conj ((Formula.mem t w).conj (.equal t a))

def terminalBody {m} (w C f g p n a : Fin m) : Formula (m+3) :=
  (edge (old 3 f) (old 3 p) (slot 3 1)).conj ((edge (old 3 g) (old 3 p) (slot 3 2)).conj
    ((StructuralListSyntax.consCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 n)).conj
      (PacketAffineSyntax.affine (old 3 w) (old 3 C) (slot 3 0) (slot 3 2) (old 3 a))))

def terminal {m} (w C f g p n a : Fin m) : Formula m := existsMany 3 (terminalBody w C f g p n a)

def consBody {m} (w C n t a : Fin m) : Formula (m+3) :=
  (StructuralListSyntax.consCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 n)).conj
    ((foldAt (old 3 w) (old 3 C) (slot 3 1) (old 3 t) (slot 3 2)).conj
      (PacketAffineSyntax.affine (old 3 w) (old 3 C) (slot 3 0) (slot 3 2) (old 3 a)))

def consCase {m} (w C n t a : Fin m) : Formula m := existsMany 3 (consBody w C n t a)

def caseAt {m} (w C n t a : Fin m) : Formula m := (nilCase w n t a).disj (consCase w C n t a)

def actualBody {m} (w n t a : Fin m) : Formula (m+3) :=
  (StructuralListSyntax.consCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 n)).conj
    ((bytes (old 3 w) (slot 3 1) (old 3 t) (slot 3 2)).conj
      (PacketAffineAcceptedSyntax.accepted true (old 3 w) (slot 3 0) (slot 3 2) (old 3 a)))

def actualCons {m} (w n t a : Fin m) : Formula m := existsMany 3 (actualBody w n t a)

def criterion {m} (w n t a : Fin m) : Formula m := (nilCase w n t a).disj (actualCons w n t a)

theorem nilCase_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (nilCase w n t a).rename ρ = nilCase (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [nilCase,Formula.rename,StructuralListSyntax.nilCode_rename]

theorem terminalBody_lift {m k} (w C f g p n a : Fin m) (ρ : Fin m → Fin k) :
    (terminalBody w C f g p n a).rename (lift 3 ρ) = terminalBody (ρ w) (ρ C) (ρ f) (ρ g) (ρ p) (ρ n) (ρ a) := by
  simp only [terminalBody,Formula.rename,edge_rename,StructuralListSyntax.consCode_rename,PacketAffineSyntax.affine_rename,lift_old,lift_slot]

theorem terminal_rename {m k} (w C f g p n a : Fin m) (ρ : Fin m → Fin k) :
    (terminal w C f g p n a).rename ρ = terminal (ρ w) (ρ C) (ρ f) (ρ g) (ρ p) (ρ n) (ρ a) := by
  simp only [terminal,existsMany_rename,terminalBody_lift]

theorem consBody_lift {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (consBody w C n t a).rename (lift 3 ρ) = consBody (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,foldAt_rename,PacketAffineSyntax.affine_rename,lift_old,lift_slot]

theorem consCase_rename {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (consCase w C n t a).rename ρ = consCase (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [consCase,existsMany_rename,consBody_lift]

theorem caseAt_rename {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (caseAt w C n t a).rename ρ = caseAt (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [caseAt,Formula.rename,nilCase_rename,consCase_rename]

theorem actualBody_lift {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (actualBody w n t a).rename (lift 3 ρ) = actualBody (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [actualBody,Formula.rename,StructuralListSyntax.consCode_rename,bytes_rename,PacketAffineAcceptedSyntax.accepted_rename,lift_old,lift_slot]

theorem actualCons_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (actualCons w n t a).rename ρ = actualCons (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [actualCons,existsMany_rename,actualBody_lift]

theorem criterion_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (criterion w n t a).rename ρ = criterion (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [criterion,Formula.rename,nilCase_rename,actualCons_rename]

theorem cons_output {m} {Γ : Context m} (w h x y n : Fin m) (he : Derives Γ (.equal y n))
    (hc : Derives Γ (StructuralListSyntax.consCode w h x y)) : Derives Γ (StructuralListSyntax.consCode w h x n) := by
  let P := StructuralListSyntax.consCode w.castSucc h.castSucc x.castSucc (Fin.last m)
  have h0 : P.instantiate y = StructuralListSyntax.consCode w h x y := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate n = StructuralListSyntax.consCode w h x n := by simp only [P,Formula.instantiate,StructuralListSyntax.consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hc))

theorem intro_terminal {m} {Γ : Context m} (w C f g p n a h x u : Fin m)
    (hx : Derives Γ (edge f p x)) (hu : Derives Γ (edge g p u)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (ha : Derives Γ (PacketAffineSyntax.affine w C h u a)) : Derives Γ (terminal w C f g p n a) := by
  apply HornBinderRules.intro_many 3 (terminalBody w C f g p n a) (SyntaxAtomSyntax.three h x u)
  exact of_eq (by simp only [terminalBody,Formula.rename,edge_rename,StructuralListSyntax.consCode_rename,PacketAffineSyntax.affine_rename,assign_old,assign_slot]; rfl)
    (.conjI hx (.conjI hu (.conjI hc ha)))

theorem intro_cons {m} {Γ : Context m} (w C n t a h x u : Fin m) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hf : Derives Γ (foldAt w C x t u)) (ha : Derives Γ (PacketAffineSyntax.affine w C h u a)) : Derives Γ (consCase w C n t a) := by
  apply HornBinderRules.intro_many 3 (consBody w C n t a) (SyntaxAtomSyntax.three h x u)
  exact of_eq (by simp only [consBody,Formula.rename,StructuralListSyntax.consCode_rename,foldAt_rename,PacketAffineSyntax.affine_rename,assign_old,assign_slot]; rfl)
    (.conjI hc (.conjI hf ha))

theorem intro_actual {m} {Γ : Context m} (w n t a h x u : Fin m) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hf : Derives Γ (bytes w x t u)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (actualCons w n t a) := by
  apply HornBinderRules.intro_many 3 (actualBody w n t a) (SyntaxAtomSyntax.three h x u)
  exact of_eq (by simp only [actualBody,Formula.rename,StructuralListSyntax.consCode_rename,bytes_rename,PacketAffineAcceptedSyntax.accepted_rename,assign_old,assign_slot]; rfl)
    (.conjI hc (.conjI hf ha))

end PPAC.Migration.Internal.PacketBytesRecursionSyntax
