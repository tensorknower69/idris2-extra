module Extra.Proof

export
unsafeRefl : {0 a, b : t} -> a === b
unsafeRefl = believe_me (the (a === a) Refl)

-- TODO: I can't do rewrite on linear types? Am I missing something
||| A poor-man's linear version of rewrite/replace
public export
replace1 : forall x, y, p . (0 rule : x = y) -> (1 _ : p x) -> p y
replace1 prf = assert_linear (replace {p = p} prf)

||| Crash the program
export total
%foreign "scheme:lambda (x) (blodwen-error-quit x)"
crash : String -> a
