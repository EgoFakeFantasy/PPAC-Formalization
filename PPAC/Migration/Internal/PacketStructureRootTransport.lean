import PPAC.Migration.Internal.ObjectPacketStructure

/-! Original equality substitutes ordered structural fields; no host value transport is used. -/
namespace PPAC.Migration.Internal.PacketStructureRootTransport
open Source SourceAlgebra SourceLogic OmegaSyntax PacketStructureSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem forest_input {m} {Γ : Context m} (w V n l t a u : Fin m)
    (he : Derives Γ (.equal n u)) (hh : Derives Γ (forestEntry w V n l t a)) : Derives Γ (forestEntry w V u l t a) := by
  let P := forestEntry w.castSucc V.castSucc (Fin.last m) l.castSucc t.castSucc a.castSucc
  have h0 : P.instantiate n = forestEntry w V n l t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = forestEntry w V u l t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem forest_length {m} {Γ : Context m} (w V n l t a u : Fin m)
    (he : Derives Γ (.equal l u)) (hh : Derives Γ (forestEntry w V n l t a)) : Derives Γ (forestEntry w V n u t a) := by
  let P := forestEntry w.castSucc V.castSucc n.castSucc (Fin.last m) t.castSucc a.castSucc
  have h0 : P.instantiate l = forestEntry w V n l t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = forestEntry w V n u t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem forest_tail {m} {Γ : Context m} (w V n l t a u : Fin m)
    (he : Derives Γ (.equal t u)) (hh : Derives Γ (forestEntry w V n l t a)) : Derives Γ (forestEntry w V n l u a) := by
  let P := forestEntry w.castSucc V.castSucc n.castSucc l.castSucc (Fin.last m) a.castSucc
  have h0 : P.instantiate t = forestEntry w V n l t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = forestEntry w V n l u a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem forest_output {m} {Γ : Context m} (w V n l t a u : Fin m)
    (he : Derives Γ (.equal a u)) (hh : Derives Γ (forestEntry w V n l t a)) : Derives Γ (forestEntry w V n l t u) := by
  let P := forestEntry w.castSucc V.castSucc n.castSucc l.castSucc t.castSucc (Fin.last m)
  have h0 : P.instantiate a = forestEntry w V n l t a := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = forestEntry w V n l t u := by
    simp only [P,Formula.instantiate,forestEntry_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem forest_row_output {m} {Γ : Context m} (w n l t a r u : Fin m)
    (he : Derives Γ (.equal a u)) (hh : Derives Γ (forestRow w n l t a r)) : Derives Γ (forestRow w n l t u r) := by
  let P := forestRow w.castSucc n.castSucc l.castSucc t.castSucc (Fin.last m) r.castSucc
  have h0 : P.instantiate a = forestRow w n l t a r := by
    simp only [P,Formula.instantiate,forestRow_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate u = forestRow w n l t u r := by
    simp only [P,Formula.instantiate,forestRow_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem empty_value {m} {Γ : Context m} (z u : Fin m)
    (he : Derives Γ (.equal z u)) (hh : Derives Γ (empty z)) : Derives Γ (empty u) := by
  let P := empty (Fin.last m)
  have h0 : P.instantiate z = empty z := by
    simp only [P,Formula.instantiate,empty_rename,Fin.lastCases_last]
  have h1 : P.instantiate u = empty u := by
    simp only [P,Formula.instantiate,empty_rename,Fin.lastCases_last]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem tree_input {m} {Γ : Context m} (w V n t a u : Fin m)
    (he : Derives Γ (.equal n u)) (hh : Derives Γ (treeEntry w V n t a)) : Derives Γ (treeEntry w V u t a) :=
  PacketTokenRootTransport.entry_first 3 w V n t a u he hh

theorem tree_tail {m} {Γ : Context m} (w V n t a u : Fin m)
    (he : Derives Γ (.equal t u)) (hh : Derives Γ (treeEntry w V n t a)) : Derives Γ (treeEntry w V n u a) :=
  PacketTokenRootTransport.entry_second 3 w V n t a u he hh

theorem tree_output {m} {Γ : Context m} (w V n t a u : Fin m)
    (he : Derives Γ (.equal a u)) (hh : Derives Γ (treeEntry w V n t a)) : Derives Γ (treeEntry w V n t u) :=
  PacketTokenRootTransport.entry_third 3 w V n t a u he hh

end PPAC.Migration.Internal.PacketStructureRootTransport
