halve
: ∀(n: Nat) Nat
= λn
  def T = λn(Nat)
  def if_succ = λnp
    def T = λn(Nat)
    def if_succ = λnpp(succ (halve npp))
    def if_zero = zero
    (~np T if_succ if_zero)
  def if_zero = zero
  (~n T if_succ if_zero)
