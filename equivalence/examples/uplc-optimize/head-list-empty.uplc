(program
  1.1.0
  (lam
    x-0
    [
      [ [ (force (builtin ifThenElse)) (con bool True) ] (con integer 7) ]
      [
        (force (builtin headList))
        [
          [
            [
              (force (builtin ifThenElse))
              [ [ (builtin equalsInteger) x-0 ] (con integer 0) ]
            ]
            (con (list integer) [])
          ]
          (con (list integer) [1])
        ]
      ]
    ]
  )
)