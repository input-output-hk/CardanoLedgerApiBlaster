(program
  1.1.0
  (lam
    x-0
    (force
      [
        [
          [ (force (builtin ifThenElse)) (con bool True) ]
          (delay (con integer 7))
        ]
        (delay [ [ (builtin divideInteger) (con integer 1) ] x-0 ])
      ]
    )
  )
)