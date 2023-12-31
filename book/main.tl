main
: ∀(x: Bool) 
  ∀(P: ∀(x:Bool) *) 
  ∀(t: (P true)) 
  ∀(f: (P false)) 
  (P x)
= λx λP λt λf 
  (~{x:Bool} λX (P X) t f)
