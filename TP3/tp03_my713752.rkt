; Cours 03 : Ordre supérieur

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [letE (s : Symbol) (rhs : Exp) (body : Exp)]
  [boolE (s : Boolean)]
  [egalE (l : Exp) (r : Exp)]
  [ifE (cond : Exp) (do : Exp) (elseCase : Exp)]
  [unletE (s : Symbol) (e : Exp)]
  [delayE (e : Exp)]
  [forceE (glacon : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [boolV (b : Boolean)]
  [freezeV (exp : Exp) (env : Env)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (val : Value)])
  

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `true s) (boolE #t)];Mettre avant sinon catch par idE
    [(s-exp-match? `false s) (boolE #f)]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]

    ;Avant appE qui a ANY ANY...
    [(s-exp-match? `{force ANY} s)
     (let ([sl (s-exp->list s)])
       (forceE (parse (second sl))))]
    
    [(s-exp-match? `{delay ANY} s)
     (let ([sl (s-exp->list s)])
       (delayE (parse (second sl))))]
    
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    
    [(s-exp-match? `{= ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (egalE (parse (second sl)) (parse (third sl))))]
    
    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (third (rest sl)))))]
    
    [(s-exp-match? `{unlet SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (unletE (s-exp->symbol (second sl))
               (parse (third sl))))]
    
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (lookup s env)]
    [(boolE b) (boolV b)]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(lamE par body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (interp arg env)) c-env))]
       [else (error 'interp "not a function")])]
    [(letE s rhs body) (interp body (extend-env (bind s (interp rhs env)) env))]
    [(egalE l r) (num= (interp l env) (interp r env))]
    [(ifE cond do elseCase) (interpIf (interp cond env) do elseCase env)]
    [(unletE s e)
     (let
         ;([newEnv (delEnv2 s env mt-env)]);Solution avec reverse moins bien...
         ([newEnv (delEnv s env)])
       (interp e newEnv))]
    [(delayE e) (freezeV e env)]
    [(forceE frz)
     (type-case Value (interp frz env)
       [(freezeV exp frzEnv)
        (interp exp frzEnv)]
       ;Je creer ici une erreur quand on a pas de delay.
       [else (error 'interp "not a thunk")])]
    ;[else (error 'interp "Not implemented")]
    ))

; Fonctions utilitaires pour l'arithmétique
(define (num-op [op : (Number Number -> Number)]
                [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (numV (op (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (num+ [l : Value] [r : Value]) : Value
  (num-op + l r))

(define (num* [l : Value] [r : Value]) : Value
  (num-op * l r))

(define (num= [l : Value] [r : Value]) : Value
  (if (and (numV? l) (numV? r))
      (boolV (= (numV-n l) (numV-n r)))
      (error 'interp "not a number")))

(define (interpIf [cond : Value] [do : Exp] [elseCase : Exp] [env : Env]) : Value
  (if (boolV? cond)
      (if (equal? (boolV-b cond) #t)
          (interp do env)
          (interp elseCase env))
      (error 'interp "not a boolean")))



; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Value
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))]
    [else (lookup n (rest env))]))

; Supression d'un identificateur dans l'environnement

(define (delEnv [n : Symbol] [env : Env]) : Env
  (cond
    ;J'ai décider d'afficher une erreur si on
    ;unlet une variable qui n'est pas dans l'environnement
    [(empty? env) (error 'delEnv "trying to unlet free identifier")]
    [(equal? n (bind-name (first env))) (rest env)]
     ;(foldr extend-env mt-env (rest env))]; == (rest env)
    [else (extend-env (first env) (delEnv n (rest env)))]))


;Autre solution : env est à l'envers -> puis on reverse
(define (delEnv2 [n : Symbol] [env : Env] [newEnv : Env]) : Env
  (cond
    [(empty? env) (error 'delEnv "trying to unlet free identifier")]
    [(equal? n (bind-name (first env)))
     (reverse (foldl extend-env newEnv (rest env)))];On doit reverse car env est a l'envers
    [else (delEnv2 n (rest env) (extend-env (first env) newEnv))]));ici le premier de env deviens le dernier.


;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))

(test (interp-expr `{let {[f {lambda {x} {+ 1 x}}]} {f 2}})
      (numV 3))

(test (interp-expr `{let {[y 1]} {lambda {x} {+ x y}}})
      (closV 'x (plusE (idE 'x) (idE 'y)) (extend-env (bind 'y (numV 1)) mt-env)))

(test (interp-expr `{let {[y 1]} {{lambda {x} {+ x y}} 2}})
      (numV 3))

(test (interp-expr `true) (boolV #t))

(test (interp-expr `false) (boolV #f))

(test (interp-expr `{if false 2 3}) (numV 3))

(test (interp-expr `{if true 2 3}) (numV 2))

(test (interp-expr `{if {= {* 2 2} {+ 1 3}} {+ 1 1} 3}) (numV 2))

(test/exn (interp-expr `{if 1 2 3}) "not a boolean")

(test (interp-expr `{if true 1 x}) (numV 1))

(test/exn (interp-expr `{let {[x 1]}
                          {unlet x x}}) "free identifier")

(test (interp-expr `{let {[x 1]}
                      {let {[x 2]}
                        {unlet x x}}})
      (numV 1))

(test (interp-expr `{let {[x 1]}
                      {let {[x 2]}
                        {+ {unlet x x} x}}})
      (numV 3))

(test (interp-expr `{let {[x 1]}
                      {let {[x 4]}
                        {let {[x 2]}
                          {let {[y 1]}
                            {let {[y 5]}
                              {+ {unlet x x} y}}}}}})
      (numV 9))



(test (interp-expr `{let {[y 1]}
                      {let {[x 4]}
                        {let {[x 2]}
                          {let {[y 7]}
                            {let {[z 5]}
                              {let {[z 3]}
                                {+ {unlet x z} y}}}}}}})
      (numV 10))

(test (interp-expr `{let {[y 1]}
                      {let {[z 5]}
                        {let {[z 3]}
                          {let {[x 4]}
                            {let {[x 2]}
                              {let {[y 7]}
                                {+ {unlet x z} y}}}}}}})
      (numV 10))

(test/exn (interp-expr `{let {[y 1]}
                          {unlet x x}}) "trying to unlet free identifier")


(test (freezeV? (interp-expr `{delay {+ 1 {lambda {x} x}}})) #t )

(test/exn (interp-expr `{force {delay {+ 1 {lambda {x} x}}}}) "not a number")

(test (interp-expr `{let {[x 1]}
                      {let {[t { delay x}]}
                        {let {[x 2]}
                          {force t}}}})
      (numV 1))

(test (interp-expr `{let {[x 1]}
                      {let {[t {delay x}]}
                        {let {[x 2]}
                          {+ {force t} x}}}})
      (numV 3))

(test/exn (interp-expr `{force 3}) "not a thunk")