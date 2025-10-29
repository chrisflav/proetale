import Mathlib.Topology.QuasiSeparated

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

-- put after `QuasiSeparatedSpace.of_isOpenEmbedding`
theorem Topology.IsClosedEmbedding.quasiSeparatedSpace [QuasiSeparatedSpace α] (h : Topology.IsClosedEmbedding f) :
    QuasiSeparatedSpace β :=
  sorry

-- after `NoetherianSpace.to_quasiSeparatedSpace`
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) :=
  sorry
