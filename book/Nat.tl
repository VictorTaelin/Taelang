Nat
: *
= $self
  ∀(P: ∀(n: Nat) *)
  ∀(s: ∀(n: Nat) (P (succ n)))
  ∀(z: (P zero))
  (P self)
