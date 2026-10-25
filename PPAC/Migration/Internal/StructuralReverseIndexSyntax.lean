import PPAC.Migration.Internal.PacketReaderTerminalContract

/-! All reverse positions satisfy the original unbounded i+j+1=l equation inside omega. -/
namespace PPAC.Migration.Internal.StructuralReverseIndexSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def witness {m} (w l i j p : Fin m) : Formula m :=
  (Formula.mem p w).conj ((sum w i j p).conj (successor l p))

def mirror {m} (w l i j : Fin m) : Formula m := (Formula.mem i w).conj ((Formula.mem j w).conj
  (.ex (witness w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m))))

def existsMirror {m} (w l i : Fin m) : Formula m := .ex (mirror w.castSucc l.castSucc i.castSucc (Fin.last m))

theorem witness_rename {m k} (w l i j p : Fin m) (ρ : Fin m → Fin k) :
    (witness w l i j p).rename ρ = witness (ρ w) (ρ l) (ρ i) (ρ j) (ρ p) := by
  simp only [witness,Formula.rename,sum_rename,successor_rename]

theorem mirror_rename {m k} (w l i j : Fin m) (ρ : Fin m → Fin k) :
    (mirror w l i j).rename ρ = mirror (ρ w) (ρ l) (ρ i) (ρ j) := by
  simp only [mirror,Formula.rename,witness_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsMirror_rename {m k} (w l i : Fin m) (ρ : Fin m → Fin k) :
    (existsMirror w l i).rename ρ = existsMirror (ρ w) (ρ l) (ρ i) := by
  simp only [existsMirror,Formula.rename,mirror_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_mirror {m} {Γ : Context m} (w l i j p : Fin m)
    (hi : Derives Γ (.mem i w)) (hj : Derives Γ (.mem j w))
    (hp : Derives Γ (witness w l i j p)) : Derives Γ (mirror w l i j) := by
  apply Derives.conjI hi
  apply Derives.conjI hj
  apply Derives.exI p
  exact of_eq (by simp only [Formula.instantiate,witness_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hp

theorem intro_exists {m} {Γ : Context m} (w l i j : Fin m) (hm : Derives Γ (mirror w l i j)) : Derives Γ (existsMirror w l i) := by
  apply Derives.exI j
  exact of_eq (by simp only [Formula.instantiate,mirror_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) hm

theorem sum_output {m} {Γ : Context m} (w i j p q : Fin m) (he : Derives Γ (.equal p q))
    (hs : Derives Γ (sum w i j p)) : Derives Γ (sum w i j q) := by
  let P := sum w.castSucc i.castSucc j.castSucc (Fin.last m)
  have h0 : P.instantiate p = sum w i j p := by simp only [P,Formula.instantiate,sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate q = sum w i j q := by simp only [P,Formula.instantiate,sum_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hs))

end PPAC.Migration.Internal.StructuralReverseIndexSyntax
