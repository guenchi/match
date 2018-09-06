# match

This is a pioneering work by ***Dan Friedman***, ***Erik Hilsdale*** and ***Kent Dybvig*** that brings pattern matching to Scheme.

It runs amazingly, and I think learning how to use it is a must-have for all Scheme users.

***Install:***

`raven install match`

***How to use:***

First of all, you have to know (match) accept a list, and matching it with you set:

You can simply use it like this:

```
(match '(a 1 2)
    ((a ,x ,y) ,x))
```    
`(a ,x ,y)` this phrase means, match the list with a symbol 'a, the car of list must be 'a not 'b or 'c.

you can write `(1 ,x ,y)` if you want to designation car to 1. or any number, or in place of cadr and caddr.

Just remenber if you use symbol or number or char, that fix there want has to be.

and the ,x ,y means it can be anything. you can call it as the last ,x in `((a ,x ,y) ,x)`, which means it back the value of x if match.

it can also accept ...

```
(match '(a 1 2 3)
    ((a ,x ...) `(,x ...)))
```    
the ... means accept any number of x, the second mean return all what it got.

so it will return '(1 2 3) and '(1 2 3 4 5) for '(a 1 2 3 4 5).

and maybe you want the x must be symbol, then do this:

```
(match '(a 1 2)
    ((a ,x ,y) (guard (symbol? x)) ,y))
``` 
(guard) need a boolean, if true this phrase match, and false not. although the list is match, but (guard) have one vote veto power, like the five permanent member in the United Nations.

Notice that the atom in test of (guard) is NOT unquote.  like (symbol? x), not (symbol? ,x).

The amazing thing is you can nesting the match:
if we define:
```
(define Expl
    (lambda (x)
        (match x
            ((a ,x) ,x))))
```
then we can use it like this: `,(Expr -> e)`
so:
```
(match '(a (a 3) 2)
    ((a ,(Expl -> e) ,y)  ,e))
```
it will return 3.

`,(Expr -> e)` test the second element and it can call by ,e.

Notice that in `,(Expr -> e)` the e is not unquote and has unquote when we call it.




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
