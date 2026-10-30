(program 1.1.0
  (lam x
    [[[(force (builtin ifThenElse)) (con bool True)]
       (con integer 1)]
       [[(builtin divideInteger) (con integer 1)] x]]))