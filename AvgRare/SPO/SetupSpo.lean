namespace AvgRare
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Placeholder structure for the SPO setup matching the paper's scope. -/
structure SetupSpo (V : Type u) [Fintype V] [DecidableEq V] : Type u :=
  (dummy : True := True.intro)

end AvgRare
