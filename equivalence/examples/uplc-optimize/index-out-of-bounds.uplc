(program
  1.1.0
  (lam
    x-0
    [
      [ [ (force (builtin ifThenElse)) (con bool True) ] (con integer 7) ]
      (force
        [
          [
            [
              (force (builtin ifThenElse))
              [ [ (builtin equalsInteger) x-0 ] (con integer 0) ]
            ]
            (delay
              [
                [ (builtin indexByteString) (con bytestring #00) ]
                (con integer 1)
              ]
            )
          ]
          (delay (con integer 1))
        ]
      )
    ]
  )
)