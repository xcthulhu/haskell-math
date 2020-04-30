theory Formula
imports Main
begin

  datatype 'a Formula =
      Implies "'a Formula" "'a Formula"   (infixr "\<Rightarrow>" 70)
    | Falsum                              ("\<^bold>\<bottom>")
    | Atom 'a

end
