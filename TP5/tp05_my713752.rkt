; Cours 05 : Les variables

#lang plait

;;;;;;;;;
; Macro ;
;;;;;;;;;

(define-syntax-rule (with [(v-id sto-id) call] body)
  (type-case Result call
    [(v*s v-id sto-id) body]))

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
  [setE (s : Symbol) (val : Exp)]
  [beginE (l : Exp) (r : Exp)]
  [addressE (s : Symbol)]
  [contentE (e : Exp)]
  [set-contentE (loc : Exp) (e : Exp)]
  [mallocE (size : Exp)]
  [freeE (pointr : Exp)])

; Représentation des valeurs
(define-type Value
  [numV (n : Number)]
  [closV (par : Symbol) (body : Exp) (env : Env)])

; Représentation du résultat d'une évaluation
(define-type Result
  [v*s (v : Value) (s : Store)])

; Représentation des liaisons
(define-type Binding
  [bind (name : Symbol) (location : Location)])

; Manipulation de l'environnement
(define-type-alias Env (Listof Binding))
(define mt-env empty)
(define extend-env cons)

; Représentation des adresses mémoire
(define-type-alias Location Number)

; Représentation d'un enregistrement
(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type Pointer
  [pointer (loc : Location) (size : Number)])

; Manipulation de la mémoire
(define-type Store
  [store (storages : (Listof Storage))
         (pointers : (Listof Pointer))])

(define mt-store (store empty empty))

(define (override-store [cell : Storage] [oldStore : Store]) : Store
  (store (cons cell (store-storages oldStore)) (store-pointers oldStore)))

(define (override-pointer [pointr : Pointer] [oldStore : Store]) : Store
  (store (store-storages oldStore) (cons pointr (store-pointers oldStore))))

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
    [(s-exp-match? `{lambda {SYMBOL} ANY} s)
     (let ([sl (s-exp->list s)])
       (lamE (s-exp->symbol (first (s-exp->list (second sl)))) (parse (third sl))))]
    [(s-exp-match? `{let [{SYMBOL ANY}] ANY} s)
     (let ([sl (s-exp->list s)])
       (let ([subst (s-exp->list (first (s-exp->list (second sl))))])
         (letE (s-exp->symbol (first subst))
               (parse (second subst))
               (parse (third sl)))))]
    [(s-exp-match? `{set! SYMBOL ANY} s)
     (let ([sl (s-exp->list s)])
       (setE (s-exp->symbol (second sl)) (parse (third sl))))]
    [(s-exp-match? `{begin ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (beginE (parse (second sl)) (parse (third sl))))]

    ;ici
    [(s-exp-match? `{address SYMBOL} s)
     (let ([sl (s-exp->list s)])
       (addressE (s-exp->symbol (second sl))))]
    [(s-exp-match? `{content ANY} s)
     (let ([sl (s-exp->list s)])
       (contentE (parse (second sl))))]
    [(s-exp-match? `{set-content! ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (set-contentE (parse (second sl)) (parse (third sl))))]
    [(s-exp-match? `{malloc ANY} s)
     (let ([sl (s-exp->list s)])
       (mallocE (parse (second sl))))]

    [(s-exp-match? `{free ANY} s)
     (let ([sl (s-exp->list s)])
       (freeE (parse (second sl))))]

    ;mettre apres sinon catch notre content et address
    [(s-exp-match? `{ANY ANY} s)
     (let ([sl (s-exp->list s)])
       (appE (parse (first sl)) (parse (second sl))))]
    [else (error 'parse "invalid input")]))

;;;;;;;;;;;;;;;;;;
; Interprétation ;
;;;;;;;;;;;;;;;;;;

; Interpréteur
(define (interp [e : Exp] [env : Env] [sto : Store]) : Result
  (type-case Exp e
    [(numE n) (v*s (numV n) sto)]
    [(idE s) (v*s (fetch (lookup s env) (store-storages sto)) sto)]
    [(plusE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num+ v-l v-r) sto-r)))]
    [(multE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (with [(v-r sto-r) (interp r env sto-l)]
                 (v*s (num* v-l v-r) sto-r)))]
    [(lamE par body) (v*s (closV par body env) sto)]
    [(appE f arg)
     (with [(v-f sto-f) (interp f env sto)]
           (type-case Value v-f
             [(closV par body c-env)
              (type-case Exp arg
                [(idE s) (interp body
                                 (extend-env (bind par (lookup s env)) c-env)
                                 sto-f)]
                [else (with [(v-arg sto-arg) (interp arg env sto-f)]
                            (let ([l (new-loc sto-arg)])
                              (interp body
                                      (extend-env (bind par l) c-env)
                                      (override-store (cell l v-arg) sto-arg))))])]
             [else (error 'interp "not a function")]))]
    [(letE s rhs body)
     (with [(v-rhs sto-rhs) (interp rhs env sto)]
           (let ([l (new-loc sto-rhs)])
             (interp body
                     (extend-env (bind s l) env)
                     (override-store (cell l v-rhs) sto-rhs))))]
    [(setE var val)
     (let ([l (lookup var env)])
       (with [(v-val sto-val) (interp val env sto)]
             (v*s v-val (override-store (cell l v-val) sto-val))))]
    [(beginE l r)
     (with [(v-l sto-l) (interp l env sto)]
           (interp r env sto-l))]

    ;MODIF ICI
    [(addressE s) (v*s (numV (lookup s env)) sto)]
    [(contentE location)
     (with [(v-loc sto-loc) (interp location env sto)]
           (type-case Value v-loc
             [(numV n) (v*s (fetch n (store-storages sto-loc)) sto-loc)]
             [else (error 'interp "segmentation fault")]
             ))]
    
    [(set-contentE location expr)
     (with [(v-loc sto-loc) (interp location env sto)]
           (type-case Value v-loc
             [(numV n) (if (and (integer? n) (< 0 n))
                           (with [(v-expr sto-expr) (interp expr env sto-loc)]
                                 (v*s v-expr (override-store (cell n v-expr) sto-expr))
                                 )
                           (error 'interp "segmentation fault"))]
             [else (error 'interp "segmentation fault")]))]

    [(mallocE sizeExp)
     (with [(v-size sto-size) (interp sizeExp env sto)]
           (type-case Value v-size
             [(numV size) (if (and (integer? size) (< 0 size))
                              (let ([firstAdd (new-loc sto-size)]);;On recupere l'adresse de la base de l'allocation.
                                ;On donne a recMalloc la memoire avec deja la premiere case faite.
                                (recMalloc (- size 1) firstAdd env (override-pointer (pointer firstAdd size) (override-store (cell firstAdd (numV 0)) sto-size))))
                              (error 'interp "not a size"))]
             [else (error 'interp "not a size")]))]

    [(freeE addrExp)
     (with [(v-addr sto-addr) (interp addrExp env sto)]
           (type-case Value v-addr
             [(numV addr)
              (let ([ptr (findPtr addr (store-pointers sto-addr))])
                (v*s
                 (numV 0)
                 (store (freeRec ptr (store-storages sto-addr))
                        (removePtr ptr (store-pointers sto-addr)))))]
             [else (error 'interp "not an allocated pointer")]))]
    ))


;ajout du tp
(define (integer? n) (= n (floor n)))

(define (recMalloc [size : Number] [firstAdd : Location] [env : Env] [sto : Store]) : Result
  (cond
    [(= size 0) (v*s (numV firstAdd) sto)]
    [else
     (let ([l (new-loc sto)])
       (recMalloc (- size 1) firstAdd env (override-store (cell l (numV 0)) sto)))]))

(define (findPtr [addr : Location] [listPtr : (Listof Pointer)]) : Pointer 
  (cond
    [(empty? listPtr) (error 'interp "not an allocated pointer")]
    [(= addr (pointer-loc (first listPtr))) (first listPtr)]
    [else (findPtr addr (rest listPtr))]))

(define (removePtr [ptr : Pointer] [listPtr : (Listof Pointer)]): (Listof Pointer)
  (cond
    [(empty? listPtr) empty]
    [(= (pointer-loc ptr) (pointer-loc (first listPtr))) (rest listPtr)]
    [else (cons (first listPtr) (removePtr ptr (rest listPtr)))]))


(define (freeRec [ptr : Pointer] [listSto : (Listof Storage)]) : (Listof Storage)
  (cond
    [(empty? listSto) empty]
    [(and;Si l'adresse de la cell est comprise entre l'adresse du pointeur et son size (strictement).
      (<= (pointer-loc ptr) (cell-location (first listSto)))
      (< (cell-location (first listSto)) (+ (pointer-loc ptr) (pointer-size ptr))))
     (freeRec ptr (rest listSto))];;On appel le reccursion sans cons
    [else (cons (first listSto) (freeRec ptr (rest listSto)))]))

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
  (+ (max-address (store-storages sto)) 1))

; Le maximum des adresses mémoires utilisés
(define (max-address [sto : (Listof Storage)]) : Location
  (if (empty? sto)
      0
      (max (cell-location (first sto)) (max-address (rest sto)))))

; Accès à un emplacement mémoire
(define (fetch [l : Location] [sto : (Listof Storage)]) : Value
  (cond
    [(empty? sto) (error 'interp "segmentation fault")]
    [(equal? l (cell-location (first sto))) (cell-val (first sto))]
    [else (fetch l (rest sto))]))

;;;;;;;;;
; Tests ;
;;;;;;;;;

(define (interp-expr [e : S-Exp]) : Value
  (v*s-v (interp (parse e) mt-env mt-store)))


(test (interp-expr `{let {[x 0]} {address x}}) (numV 1))
(test (interp-expr `{let {[x 0]} {content 1}}) (numV 0))
(test (interp-expr `{let {[x 0]}
                      {begin {set-content! 1 2}
                             x}})
      (numV 2)) 

(test (interp-expr `{let [{x 0}]
                      {set-content! {set! x 1} {+ x 1}}})
      (numV 2))

;;On ne peut rentrer une adresse negative
(test/exn (interp-expr `{let [{x 1}]
                          {set-content! -1 {+ x 1}}})
          "segmentation fault")

;;On ne peut rentrer une adresse nulle
(test/exn (interp-expr `{let [{x 1}]
                          {set-content! 0 {+ x 1}}})
          "segmentation fault")

;;On ne peut rentrer une adresse non entiere.
(test/exn (interp-expr `{let [{x 1}]
                          {set-content! 5.5 {+ x 1}}})
          "segmentation fault")

(test (interp (parse `{let {[p {malloc 3}]} p}) mt-env mt-store)
      (v*s (numV 1) (store
                     (list (cell 4 (numV 1)) ; addresse de p
                           (cell 3 (numV 0))
                           (cell 2 (numV 0))
                           (cell 1 (numV 0)))
                     (list (pointer 1 3)))))

(test (interp-expr `{malloc 5})
      (numV 1))

(test/exn (interp-expr `{malloc 0})
          "not a size")

(test/exn (interp-expr `{malloc 5.6})
          "not a size")
(test/exn (interp-expr `{malloc -1})
          "not a size")

(test (interp (parse `{let [{x 1}]
                        {begin
                          {set-content! 7 6}
                          {let {[p {malloc 8}]} p}}}) mt-env mt-store)
      (v*s (numV 8) (store
                     (list
                      (cell 16 (numV 8))
                      (cell 15 (numV 0)) (cell 14 (numV 0)) (cell 13 (numV 0)) (cell 12 (numV 0))
                      (cell 11 (numV 0)) (cell 10 (numV 0)) (cell 9 (numV 0)) (cell 8 (numV 0))
                      (cell 7 (numV 6))
                      (cell 1 (numV 1)))
                     (list
                      (pointer 8 8)))))

(test (interp (parse `{let {[p {malloc 3}]}
                        {let {[p2 {malloc 4}]}
                          p2}}) mt-env mt-store)
      (v*s (numV 5)
           (store
            (list
             (cell 9 (numV 5)) (cell 8 (numV 0))(cell 7 (numV 0))(cell 6 (numV 0))(cell 5 (numV 0))
             (cell 4 (numV 1))(cell 3 (numV 0))(cell 2 (numV 0))(cell 1 (numV 0)))
            (list
             (pointer 5 4) (pointer 1 3)))))


(test (interp (parse `{let {[p {malloc 3}]} p}) mt-env mt-store)
       (v*s (numV 1) (store (list (cell 4 (numV 1))
                                     (cell 3 (numV 0))
                                     (cell 2 (numV 0))
                                     (cell 1 (numV 0)))
                              (list (pointer 1 3)))))


(test (interp (parse `{let {[p {malloc 3}]} {free p}})
                mt-env
                mt-store )
       (v*s (numV 0) (store (list (cell 4 (numV 1)))
                              empty)))
