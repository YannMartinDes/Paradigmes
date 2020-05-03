; Cours 07 : letrec par mutation

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
  [letrecE (listS : (Listof Symbol)) (listRhs : (Listof Exp)) (body : Exp)]
  [ifE (cnd : Exp) (l : Exp) (r : Exp)]
  [lamE (par : Symbol) (body : Exp)]
  [appE (fun : Exp) (arg : Exp)]
  [pairE (fst : Exp) (snd : Exp)]
  [fstE (pair : Exp)]
  [sndE (pair : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (arg : Symbol) (body : Exp) (env : Env)]
  [pairV (fst : Thunk) (snd : Thunk)]
  [undefV])

(define-type Binding
  [bind (name : Symbol) (val : (Boxof Thunk))])

(define-type Thunk
  [delay (e : Exp) (env : Env) (mem : (Boxof (Optionof Value )))]
  [undef]) ; promesse non definie

; Représentation des liaisons
;(define-type Binding
;  [bind (name : Symbol) (val : (Boxof Value))])

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

    [(s-exp-match? `{letrec {[SYMBOL ANY] [SYMBOL ANY] ...} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sl2 (s-exp->list (second sl))])
         (letrecE (map (lambda (l) (s-exp->symbol (first (s-exp->list l)))) sl2)
                  (map (lambda (l) (parse (second (s-exp->list l)))) sl2)
                  (parse (third sl))
                  )))]

    [(s-exp-match? `{if ANY ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (ifE (parse (second sl)) (parse (third sl)) (parse (fourth sl))))]
    
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([sll (s-exp->list (second sl))])
         (lamE (s-exp->symbol (first sll)) (parse (third sl)))))]

    [(s-exp-match? `{pair ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (pairE (parse (second sl)) (parse (third sl))))]

    [(s-exp-match? `{fst ANY} s)
     (let ([sl (s-exp->list s)])
       (fstE (parse (second sl))))]

    [(s-exp-match? `{snd ANY} s)
     (let ([sl (s-exp->list s)])
       (sndE (parse (second sl))))]
    
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env]) : Value
  (type-case Exp e
    [(numE n) (numV n)]
    [(idE s) (force (lookup s env))]
    [(plusE l r) (num+ (interp l env) (interp r env))]
    [(multE l r) (num* (interp l env) (interp r env))]
    [(letrecE listS listRhs body)
     (let ([new-env (createNewEnv listS env)])
       (begin
         (setThemAll listS listRhs new-env)
         (interp body new-env)))]
    
    [(ifE cnd l r)
     (type-case Value (interp cnd env)
       [(numV n) (if (not (= n 0)) (interp l env) (interp r env))]
       [else (error 'interp "not a number")])]
    [(lamE par body) (closV par body env)]
    [(appE f arg)
     (type-case Value (interp f env)
       [(closV par body c-env)
        (interp body (extend-env (bind par (box (delay arg env (box (none))))) c-env))]
       [else (error 'interp "not a function")])]

    [(pairE fst snd)
     (pairV (delay fst env (box (none)))
            (delay snd env (box (none))))]

    [(fstE pair)
     (type-case Value (interp pair env)
       [(pairV fst snd)
        (force fst)]
       [else (error 'interp "not a pair")]
       )]
    
    [(sndE pair)
     (type-case Value (interp pair env)
       [(pairV fst snd)
        (force snd)]
       [else (error 'interp "not a pair")]
       )]
    
    ;[else (error 'interp "il reste des choses a faire")]
    ))



; FONCTIONS DU TP
(define (createNewEnv (listS : (Listof Symbol)) (env : Env)) : Env
  (cond;creer un nouvel environnement avec chaque symbol lie a une boite avec un undef.
    [(empty? listS) env]
    [else (createNewEnv (rest listS) (extend-env (bind (first listS) (box (undef))) env))]
    ))

;GROS COPIER COLLER DE LOOKUP SANS LE RENVOIE DE LA FONCTION 
(define (lookupBox [n : Symbol] [env : Env]) : (Boxof Thunk)
  (cond;recherche une boite dans un environnement selon un symbol
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (bind-val (first env))];on renvoie la boite du glaçon
    [else (lookupBox n (rest env))]))

(define (setThemAll listS listRhs new-env) : Value
  (cond
    ;les deux doivent etre vides en meme temps
    [(and (empty? listS) (empty? listRhs)) (numV 1)];Tout a été set correctement (on renvoie true)
    
    [(and (not (empty? listS)) (not (empty? listRhs)))
     (begin
       (set-box! (lookupBox (first listS) new-env);on recherche la boite a modifiée.
                 (delay (first listRhs) new-env (box (none))));on la set
       (setThemAll (rest listS) (rest listRhs) new-env));on continue avec le reste
     ]
    ;Normalement on ne peut aps attendre l'erreur car on sera rejeter par le parser avant
    [else (error 'interp "not same size")]
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

; Recherche d'un identificateur dans l'environnement
(define (lookup [n : Symbol] [env : Env]) : Thunk
  (cond
    [(empty? env) (error 'lookup "free identifier")]
    [(equal? n (bind-name (first env))) (unbox (bind-val (first env)))]
    [else (lookup n (rest env))]))


(define (force [t : Thunk]) : Value
  (type-case Thunk t
    [(delay e env mem)
     (type-case (Optionof Value) (unbox mem)
       [(none) (begin
                 (set-box! mem (some (undefV)))
                 (let ([val (interp e env)])
                   (begin
                     (set-box! mem (some val))
                     val)))]
       [(some val) val])]
    [(undef) (undefV)]
    ))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (interp (parse e) mt-env))

(test (interp-expr `{letrec {[fac {lambda {n}
                                    {if n
                                        {* n {fac {+ n -1}}}
                                        1}}]}
                      {fac 6}})
      (numV 720))
        
(test (interp-expr `{letrec {[x {0 1}]} 2})
      (numV 2))
        
(test/exn (interp-expr `{letrec {[x {0 1}]} x})
          "not a function")

(test (interp-expr `{letrec {[x x]} x})
      (undefV))

(test/exn (interp-expr `{fst {+ 1 2}})
          "not a pair")

(test/exn (interp-expr `{snd {+ 1 2}})
          "not a pair")

(test (interp-expr `{fst {pair {+ 1 2} {letrec {[x x]} x}}})
      (numV 3))

(test (interp-expr `{snd {pair {+ 1 2} {letrec {[x x]} x}}})
      (undefV))

(test (interp-expr `{fst {pair 1 x}})
      (numV 1))

(test/exn (interp-expr `{snd {pair 1 x}})
          "free identifier")

(test (interp-expr
       `{letrec {[numbers-from {lambda {n}
                                 {pair n
                                       {numbers-from {+ n 1}}}}]}
          {let {[ints {numbers-from 0}]}
            {fst {snd {snd {snd ints}}}}}})
      (numV 3))

(test (parse `{letrec {[x 1]
                       [y 2]} {+ x y}})
      (letrecE '(x y) (list (numE 1) (numE 2)) (plusE (idE 'x) (idE 'y))))

(parse `{letrec {[even? {lambda {n} {if n
                                        {odd? {- n 1} }
                                        1} }]
                 [odd? {lambda {n} {if n
                                       {even? {- n 1} }
                                       0} }]}
          {even? 5}})

(test ( interp-expr
        `{letrec {[even? {lambda {n} {if n
                                         {odd? {- n 1} }
                                         1} }]
                  [odd? {lambda {n} {if n
                                        {even? {- n 1} }
                                        0} }]}
           {even? 5}})
      (numV 0))

(test (interp-expr
       `{letrec
            {; curryfied map2 on infinite lists
             [map2 {lambda {f}
                     {lambda {l1}
                       {lambda {l2}
                         {pair {{f {fst l1}} {fst l2}}
                               {{{map2 f} {snd l1}} {snd l2}}}}}}]
             ; curryfied list-ref
             [list-ref {lambda {l}
                         {lambda {n}
                           {if n
                               {{list-ref {snd l}} {- n 1}}
                               {fst l}}}}]
             ; curryfied addition function
             [add {lambda {x} {lambda {y} {+ x y}}}]
             ; infinite fibonacci sequence !!!
             ; ( list 0 1 1 2 3 5 8 13 ... )
             [fibo {pair 0
                         {pair 1
                               {{{map2 add} fibo} {snd fibo}}}}]}
          {{list-ref fibo} 7}})
      (numV 13))

(test (interp-expr `{letrec {
                             [x {+ 2 z}]
                             [y {+ 1 x}]
                             [z 5]
                             [k 45]}
                      y})
      (numV 8))
