; Cours 08 : Continuations

#lang plait

;;;;;;;;;;;;;;;;;;;;;;;;
; Définition des types ;
;;;;;;;;;;;;;;;;;;;;;;;;

; Représentation des expressions
(define-type Exp
  [numE (n : Number)]
  [idE (s : Symbol)]
  [appE (fun : Exp) (arg : Exp)]
  [plusE (l : Exp) (r : Exp)]
  [multE (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [let/ccE (s : Symbol) (body : Exp)]
  [setE (var : Symbol) (val : Exp)]
  [beginE (l : Exp) (r : Exp)]
  [ifE (test : Exp) (true : Exp) (false : Exp)]
  [whileE (cnd : Exp) (body : Exp)]
  [breakE]
  )

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)]
  [contV (k : Cont)]
  [breakV])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (location : Location)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des continuations
(define-type Cont
  [doneK]
  [addSecondK (r : Exp) (env : Env) (k : Cont)]
  [doAddK (val : Value) (k : Cont)]
  [multSecondK (r : Exp) (env : Env) (k : Cont)]
  [doMultK (val : Value) (k : Cont)]
  [appArgK (arg : Exp) (env : Env) (k : Cont)]
  [doAppK (val : Value) (k : Cont)]
  [setK (var : Symbol) (env : Env) (k : Cont)]
  [beginK (r : Exp) (env : Env)(k : Cont)]
  [ifK (true : Exp) (false : Exp) (env : Env) (k : Cont)]
  [whileK (cnd : Exp) (body : Exp) (env : Env) (k : Cont)]
  [LoopK (cnd : Exp) (body : Exp) (env : Env) (k : Cont)]
  )

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

; Manipulation de la mémoire
(define-type-alias Store (Listof Storage))
(define mt-store empty)
(define override-store cons)

;;;;;;;;;;;;;;;;;;;;;;
; Analyse syntaxique ;
;;;;;;;;;;;;;;;;;;;;;;

(define (parse [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `break s) (breakE)]
    [(s-exp-match? `NUMBER s) (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s) (idE (s-exp->symbol s))]
    [(s-exp-match? `{+ ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{* ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (multE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{- ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (plusE (parse (second sl)) (multE (numE -1) (parse (third sl)))))]
    [(s-exp-match? `{let {[SYMBOL ANY]} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (appE (lamE (s-exp->symbol (first subst)) (parse (third sl))) (parse (second subst)))))]
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let/cc SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (let/ccE (s-exp->symbol (second sl)) (parse (third sl))))]


    ;TP ICI
    [(s-exp-match? `{set! SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (s-exp->symbol (second sl)) (parse (third sl))))]

    [(s-exp-match? `{begin ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (parse (third sl))))]

    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (third (rest sl)))))]

    [(s-exp-match? `{while ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (whileE (parse (second sl)) (parse (third sl))))]
    

    
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store] [k : Cont]) : Value
  (type-case Exp e
    [(numE n) (continue k (numV n) sto)]
    [(idE s) (continue k (fetch (lookup s env) sto) sto)]
    [(plusE l r) (interp l env sto (addSecondK r env k))]
    [(multE l r) (interp l env sto (multSecondK r env k))]
    [(lamE par body) (continue k (closV par body env) sto)]
    [(appE f arg) (interp f env sto (appArgK arg env k))]

    ;TP ICI
    [(setE var val) (interp val env sto (setK var env k))]
    [(beginE l r) (interp l env sto (beginK r env k))]

    [(ifE test true false) (interp test env sto (ifK true false env k))]

    [(whileE cnd body) (interp cnd env sto (whileK cnd body env k))]
    
    [(let/ccE s body)
     (let ([l (new-loc sto)])
       (interp body
               (extend-env (bind s l) env)
               (override-store (cell l (contV k)) sto)
               k))]
    [(breakE)
     (continue k (breakV) sto)]
    ))

; Appel des continuations
(define (continue [k : Cont] [val : Value] [sto : Store]) : Value
  (type-case Cont k
    [(doneK)
     (type-case Value val
       [(breakV) (error 'interp "break outside while")]
       [else val])]
    
    [(addSecondK r env next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (interp r env sto(doAddK val next-k))])]
    [(doAddK v-l next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (continue next-k (num+ v-l val) sto)])]
    
    [(multSecondK r env next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (interp r env sto (doMultK val next-k))])]
    
    [(doMultK v-l next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (continue next-k (num* v-l val) sto)])]
    
    [(appArgK arg env next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (interp arg env sto (doAppK val next-k))])]

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    [(setK var env next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else 
        (let ([l (lookup var env)])
          (continue next-k val (override-store (cell l val) sto)))])]

    [(beginK r env next-k)
     (type-case Value val
       [(breakV) (continue next-k (breakV) sto)]
       [else (interp r env sto next-k)])]

    [(ifK true false env next-k)
     (type-case Value val
       [(numV n)
        (if (= 0 n)
            (interp false env sto next-k)
            (interp true env sto next-k))]
       [(breakV) (continue next-k (breakV) sto)]
       [else (error 'continue "not a number")])]

    [(whileK cnd body env next-k)
     (type-case Value val
       [(numV n) (if (= 0 n)
                     (continue next-k (numV 0) sto)
                     (interp body env sto (LoopK cnd body env next-k))
                     )]
       [(breakV) (continue next-k (breakV) sto)]
       [else (error 'continue "not a number")])]

    [(LoopK cnd body env next-k)
     (type-case Value val
       [(breakV) (continue next-k (numV 0) sto)]
       [else
        (interp cnd env sto (whileK cnd body env next-k))])]
    
    [(doAppK v-f next-k)
     (type-case Value v-f
       [(breakV) (continue next-k (breakV) sto)]
       [(closV par body c-env)
        (let ([l (new-loc sto)])
          (interp body
                  (extend-env (bind par l) c-env)
                  (override-store (cell l val) sto)
                  next-k))]
       [(contV k-v) (continue k-v val sto)]
       [else (error 'interp "not a function")])]))

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

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-location (first env))]
    [else (lookup n (rest env))]))

; Renvoie une adresse mémoire libre
(define (new-loc [sto : Store]) : Location
  (+ (max-address sto) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : Store]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env mt-store (doneK)))

(test (interp-expr `{let {[x 0]}
                      {set! x 1}})
      (numV 1))

(test (interp-expr `{let {[x 0]}
                      {set! x {+ 3 2}}})
      (numV 5))

(test (interp-expr `{let {[x 0]}
                      {begin {set! x 1}
                             x}})
      (numV 1))

(test (interp-expr `{begin 0 6})
      (numV 6))

(test (interp-expr `{if 1 2 3}) (numV 2))
(test (interp-expr `{if 0 2 3}) (numV 3))


(test (interp-expr `{if {- 5 5} 2 3}) (numV 3))

(test (interp-expr `{while 0 x}) ( numV 0))
(test (interp-expr `{let {[fac
                           {lambda {n}
                             {let {[res 1]}
                               {begin
                                 {while n ; tant que n est non nul
                                        {begin
                                          {set! res {* n res}}
                                          {set! n {+ n -1}}}}
                                 res}}}]}
                      {fac 6}})
      (numV 720))

(test (interp-expr `{let {[fac
                           {lambda {n}
                             {let {[res 1]}
                               {begin
                                 {while {+ n 1}; tant que n est non nul
                                        {begin
                                          {set! res {* n res}}
                                          {set! n {+ n -1}}}}
                                 res}}}]}
                      {fac 5}})
      (numV 0))

(test (interp-expr `{let {[res 1]}
                      {let {[n 2]}
                        {begin
                          {while {+ n 1} ; tant que n est non nul
                                 {begin
                                   {set! res 5}
                                   {set! n {+ n -1}}}}
                          res}}})
      (numV 5))

(test (interp-expr `{while 1 break}) ( numV 0))

(test/exn (interp-expr `break) "break outside while")

(test/exn (interp-expr `{while break 1}) "break outside while")

(test/exn (interp-expr `{+ 1 break}) "break outside while")

(test/exn (interp-expr `{let {[x 5]}
                          {set! x break}}) "break outside while")

(test ( interp-expr `{let {[n 10]}
                       {begin
                         {while n ; tant que n est non nul
                                {if {- n 5}
                                    {set! n {- n 1}} ; si n n' egale pas 5
                                    break}} ; si n egale 5
                         n}})
      (numV 5))

(test (interp-expr `{let {[res 1]}
                      {let {[n 2]}
                        {begin
                          {while {+ n 1} ; tant que n est non nul
                                 {begin
                                   {if 0
                                       {set! n {- n 1}}
                                       break
                                       }
                                   {begin 
                                     {set! res 5}
                                     {set! n {+ n -1}}}}}
                          res}}})
      (numV 1))

(test (interp-expr `{while 1 {if break 1 2}})
      (numV 0))
(test (interp-expr `{while 1  {+ 1 break}})
      (numV 0))
(test (interp-expr `{while 1 {while break 1}})
      (numV 0))
(test (interp-expr `{while 1 {set! x break}})
      (numV 0))
(test/exn (interp-expr `{while {if break 1 2} 1})
          "break outside while")

(test (interp-expr `{let {[x 10]}
                      {begin
                        {while 1
                               {begin {set! x 42}
                                      {begin break {0 1}}}}
                        x}})
      (numV 42))