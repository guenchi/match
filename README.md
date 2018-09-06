# match
Dan Friedman, Erik Hilsdale and Kent Dybvig's match

This is a pioneering work by Dan Friedman, Erik Hilsdale and Kent Dybvig that brings pattern matching to Scheme.

It runs amazingly, and I think learning how to use it is a must-have for all Scheme users.

***install:***

`raven install match`







```
 Exp    ::= (match              Exp Clause)
         || (trace-match        Exp Clause)
         || (match+       (Id*) Exp Clause*)
         || (trace-match+ (Id*) Exp Clause*)
         || OtherSchemeExp

 Clause ::= (Pat Exp+) || (Pat (guard Exp*) Exp+)

 Pat    ::= (Pat ... . Pat)
         || (Pat . Pat)
         || ()
         || #(Pat* Pat ... Pat*)
         || #(Pat*)
         || ,Id
         || ,[Id*]
         || ,[Cata -> Id*]
         || Id

 Cata   ::= Exp
 ```

 YOU'RE NOT ALLOWED TO REFER TO CATA VARS IN GUARDS. (reasonable!)
