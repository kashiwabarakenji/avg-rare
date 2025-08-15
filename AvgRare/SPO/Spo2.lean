namespace AvgRare
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Specialised variant (e.g., singleton_if_not_maximal). -/
structure Spo2 (V : Type u) [Fintype V] [DecidableEq V] : Type u :=
  (dummy : True := True.intro)

end AvgRare
