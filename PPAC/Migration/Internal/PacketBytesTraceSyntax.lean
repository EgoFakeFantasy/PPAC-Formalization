import PPAC.Migration.Internal.PacketBytesRowSyntax

/-! Two internally finite sequences give the independent ordered byte-fold graph. -/
namespace PPAC.Migration.Internal.PacketBytesTraceSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketBytesRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def trace {m} (w C n t a z e l d f g : Fin m) : Formula m :=
  (StructuralListTraceSyntax.trace w z e l d f n).conj
    ((SequenceSyntax.sequence g d w).conj ((edge g z t).conj ((edge g l a).conj (links w C l f g))))

def body {m} (w C n t a : Fin m) : Formula (m+6) :=
  trace (old 6 w) (old 6 C) (old 6 n) (old 6 t) (old 6 a)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def foldAt {m} (w C n t a : Fin m) : Formula m := existsMany 6 (body w C n t a)

def bytes {m} (w n t a : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (foldAt w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc))

theorem trace_rename {m k} (w C n t a z e l d f g : Fin m) (ρ : Fin m → Fin k) :
    (trace w C n t a z e l d f g).rename ρ = trace (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) (ρ z) (ρ e) (ρ l) (ρ d) (ρ f) (ρ g) := by
  simp only [trace,Formula.rename,StructuralListTraceSyntax.trace_rename,SequenceSyntax.sequence_rename,edge_rename,links_rename]

theorem body_lift {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (body w C n t a).rename (lift 6 ρ) = body (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [body,trace_rename,lift_old,lift_slot]

theorem foldAt_rename {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (foldAt w C n t a).rename ρ = foldAt (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [foldAt,existsMany_rename,body_lift]

theorem bytes_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (bytes w n t a).rename ρ = bytes (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [bytes,Formula.rename,SyntaxNumeralSyntax.numeral_rename,foldAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_trace {m} {Γ : Context m} (w C n t a z e l d f g : Fin m)
    (hf : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n)) (hg : Derives Γ (SequenceSyntax.sequence g d w))
    (ht : Derives Γ (edge g z t)) (ha : Derives Γ (edge g l a)) (hl : Derives Γ (links w C l f g)) :
    Derives Γ (trace w C n t a z e l d f g) := .conjI hf (.conjI hg (.conjI ht (.conjI ha hl)))

theorem intro_fold {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (foldAt w C n t a) := by
  apply HornBinderRules.intro_many 6 (body w C n t a) (six z e l d f g)
  exact of_eq (by simp only [body,trace_rename,assign_old,assign_slot]; rfl) hf

theorem intro_bytes {m} {Γ : Context m} (w C n t a : Fin m) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C))
    (hf : Derives Γ (foldAt w C n t a)) : Derives Γ (bytes w n t a) := by
  apply Derives.exI C
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,SyntaxNumeralSyntax.numeral_rename,foldAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hC hf)

end PPAC.Migration.Internal.PacketBytesTraceSyntax
