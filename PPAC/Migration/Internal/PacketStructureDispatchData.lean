import PPAC.Migration.Internal.PacketStructureApplication

/-! Finite original table classification for tags 3, 4 and 5; no internal runtime index is externalized. -/
namespace PPAC.Migration.Internal.PacketStructureDispatchData
open YesMetaZFC.Automation
open ObjectHorn (Rule)
open PacketStructureApplicationSyntax

inductive Family where
  | tree | forest | packet

def tag : Family → Nat
  | .tree => 3
  | .forest => 4
  | .packet => 5

def width : Family → Nat
  | .tree => 3
  | .forest => 4
  | .packet => 2

def branches : Family → List Branch
  | .tree => [.tree]
  | .forest => [.nil,.cons]
  | .packet => [.packet]

def others (f : Family) : List Rule := ObjectPacket.rules.filter (fun r => PacketAffineDispatchData.differentOuter (tag f) r.head)

theorem others_different (f : Family) (r : Rule) (hr : r ∈ others f) :
    PacketAffineDispatchData.differentOuter (tag f) r.head = true := (List.mem_filter.mp hr).2

theorem branch_member (b : Branch) : rule b ∈ ObjectPacket.rules := by
  cases b <;> simp [rule,PacketStructureRuleData.treeRule,PacketStructureRuleData.nilRule,PacketStructureRuleData.consRule,PacketStructureRuleData.packetRule,ObjectPacket.rules]

theorem rule_cases (f : Family) (r : Rule) (hr : r ∈ ObjectPacket.rules) :
    (∃ b, b ∈ branches f ∧ r = rule b) ∨ r ∈ others f := by
  cases f with
  | tree =>
    simp only [ObjectPacket.rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inl ⟨.tree,by simp [branches] ,rfl⟩
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
  | forest =>
    simp only [ObjectPacket.rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inl ⟨.nil,by simp [branches] ,rfl⟩
    · exact Or.inl ⟨.cons,by simp [branches] ,rfl⟩
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
  | packet =>
    simp only [ObjectPacket.rules,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨by simp [ObjectPacket.rules] ,rfl⟩)
    · exact Or.inl ⟨.packet,by simp [branches] ,rfl⟩

end PPAC.Migration.Internal.PacketStructureDispatchData
