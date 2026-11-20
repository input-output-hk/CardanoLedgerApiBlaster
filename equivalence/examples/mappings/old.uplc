(program 1.1.0
  (lam amount (lam percent
    [[(builtin divideInteger) [[(builtin multiplyInteger) amount] percent]] (con integer 100)])))
